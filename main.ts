// mend — a CLI that applies an AI-written edit to a tree of text files (SPEC.md).
//
// Design: two phases. Phase 1 reads the patch text with cursor-based line scanners and
// produces plain data edit objects (an AST) — one object per edit, in patch order, with
// every structural fault reported before any file is looked at. Phase 2 is a separate
// apply engine that walks the AST against an in-memory file map; a failed edit rolls
// back, later edits still run, and nothing is written unless every edit succeeded.
// Line matching (SPEC section 5) lives in its own matcher section below: it exports
// occurrence-finding per tier. Node 22, standard library only.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMAT_NAMES = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** An exit-2 condition; `line` is the single line to print. */
class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One edit's failure: a code and the path the failure concerns. */
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

// ---------------------------------------------------------------- utilities

function isBlank(s: string): boolean {
  return s.trim() === '';
}

/** A patch's lines: split at \n, one trailing \r removed each, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (text.endsWith('\n')) parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A safe path (section 3): non-empty, relative, no backslash, no empty / . / .. segment. */
function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((seg) => seg !== '' && seg !== '.' && seg !== '..');
}

function byteCompare(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

// ------------------------------------------------------------ file model

interface FileModel {
  lines: string[];
  br: string; // '\r\n' or '\n'
  finalBreak: boolean;
}

/** Split a file's text at its own line break (CRLF iff its first \n follows a \r). */
function splitFile(text: string): FileModel {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function joinFile(m: FileModel): string {
  if (m.lines.length === 0) return '';
  return m.lines.join(m.br) + (m.finalBreak ? m.br : '');
}

// ------------------------------------------------- matcher (SPEC section 5)

/** Trailing spaces and tabs removed. */
function rtrimST(s: string): string {
  let end = s.length;
  while (end > 0 && (s[end - 1] === ' ' || s[end - 1] === '\t')) end -= 1;
  return s.slice(0, end);
}

/** Leading spaces and tabs removed. */
function ltrimST(s: string): string {
  let start = 0;
  while (start < s.length && (s[start] === ' ' || s[start] === '\t')) start += 1;
  return s.slice(start);
}

/** The leading spaces and tabs of a line. */
function indentOf(s: string): string {
  return s.slice(0, s.length - ltrimST(s).length);
}

/** Does one file line equal one patch line at the given tier? */
function lineMatchesAtTier(fileLine: string, patchLine: string, tier: number): boolean {
  if (tier === 0) return fileLine === patchLine;
  if (tier === 1) return rtrimST(fileLine) === rtrimST(patchLine);
  return ltrimST(rtrimST(fileLine)) === ltrimST(rtrimST(patchLine));
}

/**
 * Every start position, at or after `from`, where `oldLines` occurs in `fileLines`
 * at `tier`. When `mustEndAtFileEnd` is set, only occurrences ending at the file's
 * last line count. Occurrences may overlap.
 */
function occurrencesAtTier(fileLines: string[], oldLines: string[], tier: number, from: number, mustEndAtFileEnd: boolean): number[] {
  const found: number[] = [];
  const last = fileLines.length - oldLines.length;
  for (let i = Math.max(0, from); i <= last; i += 1) {
    if (mustEndAtFileEnd && i + oldLines.length !== fileLines.length) continue;
    let ok = true;
    for (let k = 0; k < oldLines.length; k += 1) {
      if (!lineMatchesAtTier(fileLines[i + k]!, oldLines[k]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) found.push(i);
  }
  return found;
}

interface TierHit {
  tier: number;
  positions: number[];
}

/** The first tier (0, then 1, then 2; tier 0 only when strict) with an occurrence, or null. */
function firstTierHit(fileLines: string[], oldLines: string[], strict: boolean, from: number, mustEndAtFileEnd: boolean): TierHit | null {
  const topTier = strict ? 0 : 2;
  for (let tier = 0; tier <= topTier; tier += 1) {
    const positions = occurrencesAtTier(fileLines, oldLines, tier, from, mustEndAtFileEnd);
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

/** The first tier at which a single anchor line occurs at or after `from`, and its first position. */
function anchorHit(fileLines: string[], anchor: string, strict: boolean, from: number): { tier: number; pos: number } | null {
  const topTier = strict ? 0 : 2;
  for (let tier = 0; tier <= topTier; tier += 1) {
    for (let i = Math.max(0, from); i < fileLines.length; i += 1) {
      if (lineMatchesAtTier(fileLines[i]!, anchor, tier)) return { tier, pos: i };
    }
  }
  return null;
}

/**
 * Build the replacement lines for a match. Context entries are written as the file's
 * own matched lines; at tier 2 every other new line is re-indented from the patch's
 * first old line's indent (P) to the file's first matched line's indent (F).
 */
type BodyKind = 'ctx' | 'del' | 'add';
interface BodyLine {
  kind: BodyKind;
  text: string;
  noNewline: boolean; // a `\` line follows this body line
  fromEmptyLine: boolean; // the body line was an empty patch line (a context line)
}

function buildReplacement(body: BodyLine[], fileLines: string[], pos: number, tier: number): string[] {
  const oldLines = body.filter((b) => b.kind !== 'add').map((b) => b.text);
  const fileIndent = pos < fileLines.length ? indentOf(fileLines[pos]!) : '';
  const patchIndent = oldLines.length > 0 ? indentOf(oldLines[0]!) : '';
  const out: string[] = [];
  let oi = 0;
  for (const b of body) {
    if (b.kind === 'ctx') {
      out.push(fileLines[pos + oi]!);
      oi += 1;
    } else if (b.kind === 'del') {
      oi += 1;
    } else {
      let line = b.text;
      if (tier === 2 && line !== '' && line.trim() !== '') {
        if (patchIndent === '') line = fileIndent + line;
        else if (line.startsWith(patchIndent)) line = fileIndent + line.slice(patchIndent.length);
      }
      out.push(line);
    }
  }
  return out;
}

/** The last body line that is a context or `+` line, if any. */
function lastCtxOrAdd(body: BodyLine[]): BodyLine | null {
  for (let i = body.length - 1; i >= 0; i -= 1) {
    if (body[i]!.kind !== 'del') return body[i]!;
  }
  return null;
}

// ------------------------------------------------------- in-memory file map

interface TreeState {
  orig: Map<string, string | null>; // path -> bytes before the patch (null: absent)
  now: Map<string, string | null>; // path -> bytes as the edits leave it
  moves: { oldPath: string; newPath: string }[]; // successful move edits, in order
}

function makeTree(): TreeState {
  return { orig: new Map(), now: new Map(), moves: [] };
}

function originalOf(tree: TreeState, p: string): string | null {
  if (!tree.orig.has(p)) {
    let v: string | null = null;
    try {
      if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
    } catch {
      v = null;
    }
    tree.orig.set(p, v);
  }
  return tree.orig.get(p)!;
}

function currentOf(tree: TreeState, p: string): string | null {
  return tree.now.has(p) ? tree.now.get(p)! : originalOf(tree, p);
}

function requireSafe(p: string): void {
  if (!isSafePath(p)) throw new Fail('unsafe', p);
}

function requireExisting(tree: TreeState, p: string): string {
  const t = currentOf(tree, p);
  if (t === null) throw new Fail('missing', p);
  return t;
}

function requireAbsent(tree: TreeState, p: string): void {
  if (currentOf(tree, p) !== null) throw new Fail('exists', p);
}

// ------------------------------------------------------------- edit AST
//
// Phase 1 produces these plain data objects; phase 2 (further below) applies them.

interface HunkData {
  a: number; // the A of @@ -A[,B] +C[,D] @@
  body: BodyLine[];
}

type EditData =
  | { kind: 'change'; path: string; hunks: HunkData[] }
  | { kind: 'create-lines'; path: string; hunks: HunkData[] } // unified creation: the `+` lines of all hunks
  | { kind: 'create-text'; path: string; text: string } // JSON create: file_text byte for byte
  | { kind: 'create-sr'; path: string; lines: string[] } // SEARCH/REPLACE creation
  | { kind: 'create-v4a'; path: string; lines: string[] } // V4A Add File
  | { kind: 'delete'; path: string }
  | { kind: 'move'; path: string; newPath: string; hunks: HunkData[] } // unified move (hunks may be empty)
  | { kind: 'sr-change'; path: string; oldLines: string[]; newLines: string[] }
  | { kind: 'v4a-update'; path: string; newPath: string | null; chunks: ChunkData[] }
  | { kind: 'json-str'; path: string; oldStr: string; newStr: string }
  | { kind: 'json-insert'; path: string; insertLine: number; addLines: string[] };

interface ChunkData {
  anchor: string | null;
  eof: boolean;
  body: BodyLine[];
}

// ------------------------------------------------- unified parser (sec. 6)

const HUNK_RE = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;
const GIT_RE = /^diff --git a\/(.*) b\/(.*)$/;

interface SectionData {
  gitOld: string | null;
  gitNew: string | null;
  pairOld: string | null;
  pairNew: string | null;
  hasPair: boolean;
  renameFrom: string | null;
  renameTo: string | null;
  newFileMode: boolean;
  deletedFileMode: boolean;
  hunks: HunkData[];
  isDelete: boolean; // known deletion: the rest of the section is skipped unread
}

function newSection(gitOld: string | null, gitNew: string | null): SectionData {
  return {
    gitOld,
    gitNew,
    pairOld: null,
    pairNew: null,
    hasPair: false,
    renameFrom: null,
    renameTo: null,
    newFileMode: false,
    deletedFileMode: false,
    hunks: [],
    isDelete: false,
  };
}

/** The path named by a --- / +++ header line: after the 4 chars, up to a tab, spaces removed, a/ or b/ stripped. */
function headerPath(line: string): string {
  let rest = line.slice(4);
  const tab = rest.indexOf('\t');
  if (tab >= 0) rest = rest.slice(0, tab);
  rest = rest.trim();
  if (rest.startsWith('a/') || rest.startsWith('b/')) rest = rest.slice(2);
  return rest;
}

function sectionStartsAt(lines: string[], i: number): boolean {
  const l = lines[i]!;
  if (l.startsWith('diff --git ')) return true;
  return l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ');
}

/** Does this section, as far as its header is known, describe a deletion? */
function sectionIsDelete(s: SectionData): boolean {
  if (s.deletedFileMode) return true;
  if (s.hasPair && s.pairNew === '/dev/null') return true;
  return false;
}

/** Turn a finished section into its edit object. */
function sectionToEdit(s: SectionData): EditData {
  const oldPath = s.hasPair ? s.pairOld : (s.renameFrom ?? s.gitOld);
  const newPath = s.hasPair ? s.pairNew : (s.renameTo ?? s.gitNew);
  if (s.newFileMode || (s.hasPair && s.pairOld === '/dev/null')) {
    return { kind: 'create-lines', path: newPath ?? oldPath ?? '', hunks: s.hunks };
  }
  if (s.deletedFileMode || (s.hasPair && s.pairNew === '/dev/null')) {
    return { kind: 'delete', path: oldPath ?? '' };
  }
  if (oldPath !== null && newPath !== null && oldPath !== newPath) {
    return { kind: 'move', path: oldPath, newPath, hunks: s.hunks };
  }
  return { kind: 'change', path: newPath ?? oldPath ?? '', hunks: s.hunks };
}

function parseUnified(lines: string[]): EditData[] {
  const edits: EditData[] = [];
  let sec: SectionData | null = null;
  let i = 0;

  const finishSection = (): void => {
    if (sec !== null) {
      edits.push(sectionToEdit(sec));
      sec = null;
    }
  };

  while (i < lines.length) {
    const line = lines[i]!;

    // A deletion section's remaining lines are skipped, unread and unvalidated,
    // until the next section start or the end of the patch (section 6). The
    // section's own --- / +++ header pair, when it has not been read yet, is
    // consumed as part of the section rather than treated as a new section.
    if (sec !== null && sec.isDelete) {
      if (line.startsWith('--- ') && !sec.hasPair && (lines[i + 1] ?? '').startsWith('+++ ')) {
        sec.pairOld = headerPath(line);
        sec.pairNew = headerPath(lines[i + 1]!);
        sec.hasPair = true;
        i += 2;
        continue;
      }
      if (sectionStartsAt(lines, i)) {
        finishSection();
        continue;
      }
      i += 1;
      continue;
    }

    if (line.startsWith('diff --git ')) {
      const m = GIT_RE.exec(line);
      if (m === null || m[1] === '' || m[2] === '') throw new Exit2(`error: parse ${i + 1}`);
      finishSection();
      sec = newSection(m[1]!, m[2]!);
      i += 1;
      continue;
    }

    if (line.startsWith('@@')) {
      if (sec === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = HUNK_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: HunkData = { a: Number(m[1]), body: [] };
      i += 1;
      // The body: lines starting with ' ', '-', '+', '\', or empty lines; it ends at
      // the first other line, a section start, or the end of the patch.
      while (i < lines.length) {
        const bl = lines[i]!;
        if (sectionStartsAt(lines, i)) break;
        if (bl === '') {
          hunk.body.push({ kind: 'ctx', text: '', noNewline: false, fromEmptyLine: true });
          i += 1;
        } else if (bl[0] === ' ') {
          hunk.body.push({ kind: 'ctx', text: bl.slice(1), noNewline: false, fromEmptyLine: false });
          i += 1;
        } else if (bl[0] === '-') {
          hunk.body.push({ kind: 'del', text: bl.slice(1), noNewline: false, fromEmptyLine: false });
          i += 1;
        } else if (bl[0] === '+') {
          hunk.body.push({ kind: 'add', text: bl.slice(1), noNewline: false, fromEmptyLine: false });
          i += 1;
        } else if (bl[0] === '\\') {
          const prev = hunk.body[hunk.body.length - 1];
          if (prev !== undefined) prev.noNewline = true;
          i += 1;
        } else break;
      }
      // Empty lines at the end of a body are not part of it.
      while (hunk.body.length > 0 && hunk.body[hunk.body.length - 1]!.fromEmptyLine) hunk.body.pop();
      sec.hunks.push(hunk);
      continue;
    }

    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (sec !== null && sec.hunks.length > 0) finishSection();
      if (sec === null) sec = newSection(null, null);
      sec.pairOld = headerPath(line);
      sec.pairNew = headerPath(lines[i + 1]!);
      sec.hasPair = true;
      i += 2;
      if (sectionIsDelete(sec)) sec.isDelete = true;
      continue;
    }

    if (sec !== null && sec.hunks.length === 0) {
      // Section header lines, before the first hunk.
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('+++ ')) {
        // A +++ line not consumed with its --- line: name the new path from it.
        if (!sec.hasPair) {
          sec.pairNew = headerPath(line);
        }
        i += 1;
        continue;
      }
      if (line.startsWith('rename from ')) sec.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) sec.renameTo = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) sec.newFileMode = true;
      else if (line.startsWith('deleted file mode')) {
        sec.deletedFileMode = true;
        sec.isDelete = true;
      }
      i += 1;
      continue;
    }

    // Anything else outside a body is ignored prose.
    i += 1;
  }
  finishSection();
  return edits;
}

// ------------------------------------------- SEARCH/REPLACE parser (sec. 7)

function parseSearchReplace(lines: string[]): EditData[] {
  const edits: EditData[] = [];
  let prevPath: string | null = null;
  let searchFrom = 0; // lines before this index belong to earlier blocks
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchLine = i;
    // The path: the nearest line before SEARCH, after the previous block, that is
    // not blank and does not (trimmed) start with three backticks.
    let path: string | null = null;
    for (let j = searchLine - 1; j >= searchFrom; j -= 1) {
      const cand = lines[j]!;
      if (isBlank(cand)) continue;
      const trimmed = cand.trim();
      if (trimmed.startsWith('```')) continue;
      path = trimmed;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    // Find ======= and then >>>>>>> REPLACE after the SEARCH line.
    let eq = -1;
    for (let j = searchLine + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    let rep = -1;
    if (eq >= 0) {
      for (let j = eq + 1; j < lines.length; j += 1) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          rep = j;
          break;
        }
      }
    }
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    const oldLines = lines.slice(searchLine + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    if (oldLines.length === 0) edits.push({ kind: 'create-sr', path, lines: newLines });
    else edits.push({ kind: 'sr-change', path, oldLines, newLines });
    prevPath = path;
    i = rep + 1;
    searchFrom = rep + 1;
  }
  return edits;
}

// ------------------------------------------------------- V4A parser (sec. 8)

const V4A_PREFIXES = ['*** Add File: ', '*** Delete File: ', '*** Update File: '];

function v4aSectionStart(line: string): string | null {
  for (const p of V4A_PREFIXES) if (line.startsWith(p)) return p;
  return null;
}

function parseV4a(lines: string[]): EditData[] {
  let first = -1;
  let last = -1;
  for (let i = 0; i < lines.length; i += 1) {
    if (!isBlank(lines[i]!)) {
      if (first < 0) first = i;
      last = i;
    }
  }
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);

  const edits: EditData[] = [];
  let i = first + 1;
  while (i < last) {
    if (isBlank(lines[i]!)) {
      i += 1;
      continue;
    }
    const prefix = v4aSectionStart(lines[i]!);
    if (prefix === null) throw new Exit2(`error: parse ${i + 1}`);
    const sectionLine = i;
    const path = lines[i]!.slice(prefix.length).trim();
    i += 1;
    // The section's body runs to the next section start or to *** End Patch;
    // blank lines at its end are not part of it.
    const bodyStart = i;
    let bodyEnd = i;
    let j = i;
    while (j < last && v4aSectionStart(lines[j]!) === null) {
      if (!isBlank(lines[j]!)) bodyEnd = j + 1;
      j += 1;
    }
    const body = lines.slice(bodyStart, bodyEnd);
    i = j;

    if (prefix === '*** Add File: ') {
      const fileLines: string[] = [];
      for (let k = 0; k < body.length; k += 1) {
        const bl = body[k]!;
        if (bl.startsWith('+')) fileLines.push(bl.slice(1));
        else if (bl === '') fileLines.push('');
        else throw new Exit2(`error: parse ${bodyStart + k + 1}`);
      }
      edits.push({ kind: 'create-v4a', path, lines: fileLines });
      continue;
    }

    if (prefix === '*** Delete File: ') {
      for (let k = 0; k < body.length; k += 1) {
        if (!isBlank(body[k]!)) throw new Exit2(`error: parse ${bodyStart + k + 1}`);
      }
      edits.push({ kind: 'delete', path });
      continue;
    }

    // Update File: an optional Move to as its first line, then chunks.
    let newPath: string | null = null;
    const chunks: ChunkData[] = [];
    let current: ChunkData | null = null;
    let chunkClosed = false; // a *** End of File line closed the current chunk
    let k = 0;
    if (body.length > 0 && body[0]!.startsWith('*** Move to: ')) {
      newPath = body[0]!.slice('*** Move to: '.length).trim();
      k = 1;
    }
    for (; k < body.length; k += 1) {
      const bl = body[k]!;
      const lineNo = bodyStart + k + 1;
      if (bl.startsWith('@@')) {
        const anchorText = bl.slice(2).trim();
        current = { anchor: anchorText === '' ? null : anchorText, eof: false, body: [] };
        chunks.push(current);
        chunkClosed = false;
      } else if (bl.trim() === '*** End of File') {
        if (current === null) {
          current = { anchor: null, eof: true, body: [] };
          chunks.push(current);
        } else {
          current.eof = true;
        }
        current = null;
        chunkClosed = true;
      } else if (bl === '' || bl[0] === ' ' || bl[0] === '-' || bl[0] === '+') {
        if (current === null) {
          if (chunks.length > 0 || chunkClosed) throw new Exit2(`error: parse ${lineNo}`);
          current = { anchor: null, eof: false, body: [] };
          chunks.push(current);
        }
        if (bl === '') current.body.push({ kind: 'ctx', text: '', noNewline: false, fromEmptyLine: true });
        else if (bl[0] === ' ') current.body.push({ kind: 'ctx', text: bl.slice(1), noNewline: false, fromEmptyLine: false });
        else if (bl[0] === '-') current.body.push({ kind: 'del', text: bl.slice(1), noNewline: false, fromEmptyLine: false });
        else current.body.push({ kind: 'add', text: bl.slice(1), noNewline: false, fromEmptyLine: false });
      } else {
        throw new Exit2(`error: parse ${lineNo}`);
      }
    }
    if (chunks.length === 0 && newPath === null) throw new Exit2(`error: parse ${sectionLine + 1}`);
    edits.push({ kind: 'v4a-update', path, newPath, chunks });
  }
  return edits;
}

// ------------------------------------------------------ JSON parser (sec. 9)

/** One JSON edit object as data, or null when it is not a valid edit object. */
function jsonEditData(v: unknown): EditData | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  if (o.command === 'create' && typeof o.file_text === 'string') {
    return { kind: 'create-text', path: p, text: o.file_text };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    return { kind: 'json-str', path: p, oldStr: o.old_str, newStr: (o.new_str as string | undefined) ?? '' };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    return { kind: 'json-insert', path: p, insertLine: o.insert_line, addLines: patchLines(o.new_str) };
  }
  return null;
}

function parseJson(text: string, lines: string[]): EditData[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: EditData[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEditData(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, idx) => {
    if (isBlank(l)) return;
    let e: EditData | null = null;
    try {
      e = jsonEditData(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${idx + 1}`);
    edits.push(e);
  });
  return edits;
}

// ------------------------------------------------- format detection (sec. 4)

function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, idx) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[idx + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

function parsePatch(kind: string, text: string, lines: string[]): EditData[] {
  if (kind === 'json') return parseJson(text, lines);
  if (kind === 'unified') return parseUnified(lines);
  if (kind === 'search-replace') return parseSearchReplace(lines);
  return parseV4a(lines);
}

// ------------------------------------------------------------ apply engine
//
// Phase 2: walk the AST against the in-memory file map. Each edit checks every
// path it names for safety before anything else about it.

/** Apply a section's hunks in order to a file model; returns the new model. */
function applyHunks(model: FileModel, hunks: HunkData[], failPath: string, strict: boolean): FileModel {
  const lines = [...model.lines];
  let finalBreak = model.finalBreak;
  let d = 0;
  for (const hunk of hunks) {
    const oldLines = hunk.body.filter((b) => b.kind !== 'add').map((b) => b.text);
    const newCount = hunk.body.filter((b) => b.kind !== 'del').length;
    if (oldLines.length === 0) {
      const insertAt = Math.min(Math.max(hunk.a + d, 0), lines.length);
      const inserted = hunk.body.filter((b) => b.kind === 'add').map((b) => b.text);
      const atEnd = insertAt === lines.length;
      lines.splice(insertAt, 0, ...inserted);
      if (atEnd) {
        const last = lastCtxOrAdd(hunk.body);
        finalBreak = !(last !== null && last.noNewline);
      }
      d += newCount;
      continue;
    }
    const hit = firstTierHit(lines, oldLines, strict, 0, false);
    if (hit === null) throw new Fail('no-match', failPath);
    const target = hunk.a - 1 + d;
    let pos = hit.positions[0]!;
    for (const cand of hit.positions) {
      if (Math.abs(cand - target) < Math.abs(pos - target)) pos = cand;
    }
    const runsToEnd = pos + oldLines.length === lines.length;
    const replacement = buildReplacement(hunk.body, lines, pos, hit.tier);
    lines.splice(pos, oldLines.length, ...replacement);
    if (runsToEnd) {
      const last = lastCtxOrAdd(hunk.body);
      finalBreak = !(last !== null && last.noNewline);
    }
    d += newCount - oldLines.length;
  }
  return { lines, br: model.br, finalBreak };
}

function applyEdit(tree: TreeState, edit: EditData, strict: boolean): void {
  switch (edit.kind) {
    case 'change': {
      requireSafe(edit.path);
      const model = splitFile(requireExisting(tree, edit.path));
      tree.now.set(edit.path, joinFile(applyHunks(model, edit.hunks, edit.path, strict)));
      return;
    }
    case 'create-lines': {
      requireSafe(edit.path);
      requireAbsent(tree, edit.path);
      const adds: BodyLine[] = [];
      for (const h of edit.hunks) for (const b of h.body) if (b.kind === 'add') adds.push(b);
      if (adds.length === 0) {
        tree.now.set(edit.path, '');
        return;
      }
      const lastAdd = adds[adds.length - 1]!;
      tree.now.set(edit.path, adds.map((b) => b.text).join('\n') + (lastAdd.noNewline ? '' : '\n'));
      return;
    }
    case 'create-text': {
      requireSafe(edit.path);
      requireAbsent(tree, edit.path);
      tree.now.set(edit.path, edit.text);
      return;
    }
    case 'create-sr': {
      requireSafe(edit.path);
      requireAbsent(tree, edit.path);
      tree.now.set(edit.path, edit.lines.length === 0 ? '' : edit.lines.join('\n') + '\n');
      return;
    }
    case 'create-v4a': {
      requireSafe(edit.path);
      requireAbsent(tree, edit.path);
      tree.now.set(edit.path, edit.lines.length === 0 ? '' : edit.lines.join('\n') + '\n');
      return;
    }
    case 'delete': {
      requireSafe(edit.path);
      requireExisting(tree, edit.path);
      tree.now.set(edit.path, null);
      return;
    }
    case 'move': {
      requireSafe(edit.path);
      requireSafe(edit.newPath);
      const model = splitFile(requireExisting(tree, edit.path));
      requireAbsent(tree, edit.newPath);
      const result = applyHunks(model, edit.hunks, edit.path, strict);
      tree.now.set(edit.newPath, joinFile(result));
      tree.now.set(edit.path, null);
      tree.moves.push({ oldPath: edit.path, newPath: edit.newPath });
      return;
    }
    case 'sr-change': {
      requireSafe(edit.path);
      const model = splitFile(requireExisting(tree, edit.path));
      const hit = firstTierHit(model.lines, edit.oldLines, strict, 0, false);
      if (hit === null) throw new Fail('no-match', edit.path);
      if (hit.positions.length > 1) throw new Fail('ambiguous', edit.path);
      const pos = hit.positions[0]!;
      // No context lines here: build the replacement from the old lines as
      // deletions plus the new lines as additions, so the tier-2 re-indent is
      // taken from the match.
      const replacement = buildReplacement(
        [...edit.oldLines.map((t): BodyLine => ({ kind: 'del', text: t, noNewline: false, fromEmptyLine: false })), ...edit.newLines.map((t): BodyLine => ({ kind: 'add', text: t, noNewline: false, fromEmptyLine: false }))],
        model.lines,
        pos,
        hit.tier,
      );
      const lines = [...model.lines];
      lines.splice(pos, edit.oldLines.length, ...replacement);
      tree.now.set(edit.path, joinFile({ lines, br: model.br, finalBreak: model.finalBreak }));
      return;
    }
    case 'v4a-update': {
      requireSafe(edit.path);
      if (edit.newPath !== null) requireSafe(edit.newPath);
      const model = splitFile(requireExisting(tree, edit.path));
      if (edit.newPath !== null) requireAbsent(tree, edit.newPath);
      const lines = [...model.lines];
      let cursor = 0;
      for (const chunk of edit.chunks) {
        if (chunk.anchor !== null) {
          const anchor = anchorHit(lines, chunk.anchor, strict, cursor);
          if (anchor === null) throw new Fail('no-match', edit.path);
          cursor = anchor.pos + 1;
        }
        const oldLines = chunk.body.filter((b) => b.kind !== 'add').map((b) => b.text);
        if (oldLines.length === 0) {
          const inserted = chunk.body.filter((b) => b.kind === 'add').map((b) => b.text);
          const insertAt = chunk.eof ? lines.length : Math.min(cursor, lines.length);
          lines.splice(insertAt, 0, ...inserted);
          cursor = insertAt + inserted.length;
          continue;
        }
        const hit = firstTierHit(lines, oldLines, strict, cursor, chunk.eof);
        if (hit === null) throw new Fail('no-match', edit.path);
        const pos = hit.positions[0]!;
        const replacement = buildReplacement(chunk.body, lines, pos, hit.tier);
        lines.splice(pos, oldLines.length, ...replacement);
        cursor = pos + replacement.length;
      }
      const out = joinFile({ lines, br: model.br, finalBreak: model.finalBreak });
      if (edit.newPath !== null) {
        tree.now.set(edit.newPath, out);
        tree.now.set(edit.path, null);
        tree.moves.push({ oldPath: edit.path, newPath: edit.newPath });
      } else {
        tree.now.set(edit.path, out);
      }
      return;
    }
    case 'json-str': {
      requireSafe(edit.path);
      const before = requireExisting(tree, edit.path);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const toLf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = toLf(before);
      const old = toLf(edit.oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', edit.path);
      if (count > 1) throw new Fail('ambiguous', edit.path);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + toLf(edit.newStr) + t.slice(at + old.length);
      tree.now.set(edit.path, crlf ? out.replaceAll('\n', '\r\n') : out);
      return;
    }
    case 'json-insert': {
      requireSafe(edit.path);
      const before = requireExisting(tree, edit.path);
      const model = splitFile(before);
      if (edit.insertLine < 0 || edit.insertLine > model.lines.length) throw new Fail('no-match', edit.path);
      const lines = [...model.lines];
      lines.splice(edit.insertLine, 0, ...edit.addLines);
      tree.now.set(edit.path, joinFile({ lines, br: model.br, finalBreak: model.finalBreak }));
      return;
    }
  }
}

// ----------------------------------------------------------------- the CLI

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMAT_NAMES.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: EditData[];
  try {
    edits = parsePatch(kind, text, lines);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = makeTree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const beforeNow = new Map(tree.now);
    const beforeMoves = tree.moves.length;
    try {
      applyEdit(tree, edit, strict);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of beforeNow) tree.now.set(k, v);
      tree.moves.length = beforeMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  }
  // Changed paths, with a qualifying move's D+A pair replaced by one R line.
  const changed = [...tree.now.keys()].filter((p) => originalOf(tree, p) !== tree.now.get(p)!);
  const rByNew = new Map<string, string>();
  for (const mv of tree.moves) {
    if (originalOf(tree, mv.oldPath) === null) continue;
    if (currentOf(tree, mv.oldPath) !== null) continue;
    if (originalOf(tree, mv.newPath) !== null) continue;
    if (currentOf(tree, mv.newPath) === null) continue;
    rByNew.set(mv.newPath, mv.oldPath);
  }
  const rOlds = new Set(rByNew.values());
  interface Row {
    sortKey: string;
    text: string;
    path: string;
    value: string | null;
  }
  const rows: Row[] = [];
  for (const p of changed) {
    if (rOlds.has(p)) continue;
    const was = originalOf(tree, p);
    const now = tree.now.get(p)!;
    if (rByNew.has(p)) rows.push({ sortKey: p, text: `R ${rByNew.get(p)!} -> ${p}`, path: p, value: now });
    else rows.push({ sortKey: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`, path: p, value: now });
  }
  rows.sort((x, y) => byteCompare(x.sortKey, y.sortKey));
  if (!check) {
    for (const row of rows) {
      if (rByNew.has(row.path)) {
        // A move: write the new path, remove the old one.
        mkdirSync(dirname(row.path), { recursive: true });
        writeFileSync(row.path, row.value!);
        rmSync(rByNew.get(row.path)!, { force: true });
      } else if (row.value === null) {
        rmSync(row.path, { force: true });
      } else {
        mkdirSync(dirname(row.path), { recursive: true });
        writeFileSync(row.path, row.value);
      }
    }
    // Any changed path not covered above (the old side of a move) is handled by
    // its R row; nothing else remains.
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
