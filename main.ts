// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`.
//
// It does all ten sections of SPEC.md: the command line, the output and exit codes,
// safe paths, format detection, three-tier line matching, unified diffs, SEARCH/REPLACE
// blocks, V4A patches, JSON edits, and the all-or-nothing write. In a trial the grader
// runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to
// runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** A move an edit applied, for the `R old -> new` output line (section 2). */
interface MoveRec {
  old: string;
  new: string;
}

// ---------------------------------------------------------------------------
// Section 3: a file's lines, its line break, and whether it ends with one.
// ---------------------------------------------------------------------------

interface FileState {
  br: string;
  lines: string[];
  ends: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { br: '\n', lines: [], ends: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const ends = text.endsWith(br);
  if (ends) parts.pop();
  return { br, lines: parts, ends };
}

function serializeFile(st: FileState): string {
  if (st.lines.length === 0) return '';
  return st.lines.join(st.br) + (st.ends ? st.br : '');
}

// ---------------------------------------------------------------------------
// Section 5: matching lines at three tiers, and re-indenting new lines.
// ---------------------------------------------------------------------------

/** One line of an old block O or a new block N; `ctx` marks a context line. */
interface OItem {
  text: string;
  ctx: boolean;
}

const rtrimWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rtrimWs(a) === rtrimWs(b);
  return trimWs(a) === trimWs(b);
}

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

/** At tier 2, a non-context new line starting with P has that P replaced by F. */
function reindent(line: string, p: string, f: string): string {
  if (/^\s*$/.test(line)) return line;
  if (line.startsWith(p)) return f + line.slice(p.length);
  return line;
}

/** Every position where `pat` occurs in `lines` at one tier; occurrences may overlap. */
function occurrences(lines: string[], pat: string[], tier: number): number[] {
  const out: number[] = [];
  if (pat.length === 0) return out;
  for (let i = 0; i + pat.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < pat.length; j++) {
      if (!lineEq(pat[j], lines[i + j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

interface TierHit {
  tier: number;
  positions: number[];
}

/** The first tier (0, then 1, then 2; only 0 when strict) at which `pat` occurs. */
function findTier(lines: string[], pat: string[], strict: boolean): TierHit | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const pos = occurrences(lines, pat, t);
    if (pos.length > 0) return { tier: t, positions: pos };
  }
  return null;
}

/** Like findTier, but occurrences must start at or after `from`; when `eof` they must
 * also end at the file's last line (V4A end-of-file chunks, section 8). */
function findTierFrom(lines: string[], pat: string[], from: number, strict: boolean, eof: boolean): TierHit | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const pos: number[] = [];
    for (let i = from; i + pat.length <= lines.length; i++) {
      if (eof && i + pat.length !== lines.length) continue;
      let ok = true;
      for (let j = 0; j < pat.length; j++) {
        if (!lineEq(pat[j], lines[i + j]!, t)) {
          ok = false;
          break;
        }
      }
      if (ok) pos.push(i);
    }
    if (pos.length > 0) return { tier: t, positions: pos };
  }
  return null;
}

/** A V4A anchor (section 8): the first line at or after `cursor` equal to the anchor,
 * at the first tier where one is (both sides a single line). -1 when there is none. */
function findAnchorLine(lines: string[], anchor: string, cursor: number, strict: boolean): number {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = cursor; i < lines.length; i++) {
      if (lineEq(anchor, lines[i]!, t)) return i;
    }
  }
  return -1;
}

/** The lines that replace a matched block: context lines are written as the file's own
 * matched lines, never the patch's; at tier 2 every other new line is re-indented. */
function buildReplacement(oItems: OItem[], nItems: OItem[], fileLines: string[], pos: number, tier: number): string[] {
  const oCtxIdx: number[] = [];
  oItems.forEach((it, idx) => {
    if (it.ctx) oCtxIdx.push(idx);
  });
  let ctxCount = 0;
  const p = oItems.length > 0 ? leadingWs(oItems[0]!.text) : '';
  const f = fileLines.length > pos ? leadingWs(fileLines[pos]!) : '';
  return nItems.map((it) => {
    if (it.ctx) {
      const oi = oCtxIdx[ctxCount++]!;
      return fileLines[pos + oi]!;
    }
    if (tier === 2) return reindent(it.text, p, f);
    return it.text;
  });
}

// ---------------------------------------------------------------------------
// Body lines, shared by unified hunks (section 6) and V4A chunks (section 8).
// ---------------------------------------------------------------------------

type BodyKind = 'ctx' | 'old' | 'new' | 'bs';
interface BodyItem {
  kind: BodyKind;
  text: string;
}

function bodyItem(line: string): BodyItem {
  if (line === '') return { kind: 'ctx', text: '' };
  const c = line[0]!;
  if (c === ' ') return { kind: 'ctx', text: line.slice(1) };
  if (c === '-') return { kind: 'old', text: line.slice(1) };
  if (c === '+') return { kind: 'new', text: line.slice(1) };
  return { kind: 'bs', text: line.slice(1) };
}

/** Split body items into O (context and old lines) and N (context and new lines). */
function splitItems(items: BodyItem[]): { o: OItem[]; n: OItem[] } {
  const o: OItem[] = [];
  const n: OItem[] = [];
  for (const it of items) {
    if (it.kind === 'ctx') {
      o.push({ text: it.text, ctx: true });
      n.push({ text: it.text, ctx: true });
    } else if (it.kind === 'old') {
      o.push({ text: it.text, ctx: false });
    } else if (it.kind === 'new') {
      n.push({ text: it.text, ctx: false });
    }
  }
  return { o, n };
}

/** Whether a `\` line follows the hunk's last context or `+` line (section 6). */
function bsFollowsLastCtxOrNew(items: BodyItem[]): boolean {
  let last = -1;
  for (let i = 0; i < items.length; i++) {
    if (items[i]!.kind === 'ctx' || items[i]!.kind === 'new') last = i;
  }
  if (last < 0) return false;
  return items[last + 1] !== undefined && items[last + 1]!.kind === 'bs';
}

// ---------------------------------------------------------------------------
// Section 6: unified diffs.
// ---------------------------------------------------------------------------

interface Hunk {
  /** A from `@@ -A[,B] +C[,D] @@`; B and D are not used. */
  a: number;
  items: BodyItem[];
}

interface UniSection {
  pairOld: string | null | undefined;
  pairNew: string | null | undefined;
  gitOld: string | undefined;
  gitNew: string | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  hasPair: boolean;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

/** The path after `--- ` / `+++ `: text after the four characters, up to the first
 * tab, with surrounding spaces removed; a leading `a/` or `b/` is removed. */
function headerPath(line: string): string {
  const p = line
    .slice(4)
    .split('\t')[0]!
    .trim();
  return p.replace(/^[ab]\//, '');
}

function devNull(p: string): string | null {
  return p === '/dev/null' ? null : p;
}

/** A hunk's body: the lines after the header starting with ` `, `-`, `+` or `\`,
 * or empty; it ends at the first other line, at a `diff --git ` line, at a `--- `
 * line followed by a `+++ ` line, or at the end of the patch. Empty lines at the
 * end of a body are not part of it. Returns the items and the next line to read. */
function collectBody(lines: string[], start: number): { items: BodyItem[]; next: number } {
  const raw: string[] = [];
  let i = start;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
    if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) {
      raw.push(l);
      i++;
    } else {
      break;
    }
  }
  while (raw.length > 0 && raw[raw.length - 1] === '') raw.pop();
  return { items: raw.map(bodyItem), next: i };
}

/** Apply one section's hunks to a file's lines, in order, each to the result of the
 * ones before it (section 6). `d` tracks the running length change. */
function applyHunks(st: FileState, hunks: Hunk[], strict: boolean, path: string): void {
  let d = 0;
  for (const h of hunks) {
    const { o, n } = splitItems(h.items);
    if (o.length === 0) {
      const insAt = Math.max(0, Math.min(h.a + d, st.lines.length));
      const atEnd = insAt === st.lines.length;
      const added = n.map((x) => x.text);
      st.lines.splice(insAt, 0, ...added);
      if (atEnd) st.ends = !bsFollowsLastCtxOrNew(h.items);
      d += added.length;
      continue;
    }
    const found = findTier(st.lines, o.map((x) => x.text), strict);
    if (found === null) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let best = found.positions[0]!;
    let bestDist = Math.abs(best - target);
    for (const p of found.positions) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const pos = best;
    const runsToEnd = pos + o.length === st.lines.length;
    const repl = buildReplacement(o, n, st.lines, pos, found.tier);
    st.lines.splice(pos, o.length, ...repl);
    if (runsToEnd) st.ends = !bsFollowsLastCtxOrNew(h.items);
    d += n.length - o.length;
  }
}

function unifiedSectionEdit(sec: UniSection, strict: boolean, moves: MoveRec[]): Edit | null {
  let oldP: string | null | undefined;
  let newP: string | null | undefined;
  if (sec.hasPair) {
    oldP = sec.pairOld;
    newP = sec.pairNew;
  } else {
    oldP = sec.renameFrom ?? sec.gitOld;
    newP = sec.renameTo ?? sec.gitNew;
  }
  if (oldP === undefined && newP === undefined) return null;
  if (oldP === undefined) oldP = newP;
  if (newP === undefined) newP = oldP;
  if (oldP === null && newP === null) return null;
  const oldPath = oldP as string | null;
  const newPath = newP as string | null;
  const isCreate = (oldPath === null || sec.newFile) && newPath !== null;
  const isDelete = !isCreate && (newPath === null || sec.deletedFile) && oldPath !== null;
  const isMove = !isCreate && !isDelete && oldPath !== null && newPath !== null && oldPath !== newPath;

  if (isCreate) {
    const np = newPath as string;
    return (tree) => {
      if (!safe(np)) throw new Fail('unsafe', np);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const plus: string[] = [];
      let ends = true;
      for (const h of sec.hunks) {
        for (let k = 0; k < h.items.length; k++) {
          const it = h.items[k]!;
          if (it.kind === 'new') {
            plus.push(it.text);
            ends = !(h.items[k + 1] !== undefined && h.items[k + 1]!.kind === 'bs');
          }
        }
      }
      tree.now.set(np, plus.length === 0 ? '' : plus.join('\n') + (ends ? '\n' : ''));
    };
  }
  if (isDelete) {
    const op = oldPath as string;
    return (tree) => {
      if (!safe(op)) throw new Fail('unsafe', op);
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
    };
  }
  const op = oldPath as string;
  return (tree) => {
    if (!safe(op)) throw new Fail('unsafe', op);
    let np: string | null = null;
    if (isMove) {
      np = newPath as string;
      if (!safe(np)) throw new Fail('unsafe', np);
    }
    const before = tree.get(op);
    if (before === null) throw new Fail('missing', op);
    if (isMove && tree.get(np!) !== null) throw new Fail('exists', np!);
    const st = parseFile(before);
    applyHunks(st, sec.hunks, strict, op);
    const content = serializeFile(st);
    if (isMove) {
      tree.now.set(op, null);
      tree.now.set(np!, content);
      moves.push({ old: op, new: np! });
    } else {
      tree.now.set(op, content);
    }
  };
}

function unifiedEdits(lines: string[], strict: boolean, moves: MoveRec[]): Edit[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let inHeader = false;
  const fresh = (): UniSection => ({
    pairOld: undefined,
    pairNew: undefined,
    gitOld: undefined,
    gitNew: undefined,
    renameFrom: undefined,
    renameTo: undefined,
    hasPair: false,
    newFile: false,
    deletedFile: false,
    hunks: [],
  });
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = fresh();
      cur.gitOld = m[1]!;
      cur.gitNew = m[2]!;
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && inHeader && !cur.hasPair) {
        cur.pairOld = devNull(headerPath(line));
        cur.pairNew = devNull(headerPath(lines[i + 1]!));
        cur.hasPair = true;
        i += 2;
        continue;
      }
      cur = fresh();
      cur.pairOld = devNull(headerPath(line));
      cur.pairNew = devNull(headerPath(lines[i + 1]!));
      cur.hasPair = true;
      sections.push(cur);
      inHeader = true;
      i += 2;
      continue;
    }
    if (line.startsWith('--- ')) {
      if (cur !== null && inHeader) throw new Exit2(`error: parse ${i + 2}`);
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(.*)$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const body = collectBody(lines, i + 1);
      cur.hunks.push({ a: parseInt(m[1]!, 10), items: body.items });
      inHeader = false;
      i = body.next;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('rename from ')) cur.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) cur.renameTo = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.newFile = true;
      else if (line.startsWith('deleted file mode')) cur.deletedFile = true;
    }
    i++;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  for (const s of sections) {
    const e = unifiedSectionEdit(s, strict, moves);
    if (e !== null) edits.push(e);
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

// ---------------------------------------------------------------------------
// Section 7: SEARCH/REPLACE blocks.
// ---------------------------------------------------------------------------

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const st = parseFile(before);
    const found = findTier(st.lines, oldLines, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = found.positions[0]!;
    const oItems: OItem[] = oldLines.map((t) => ({ text: t, ctx: false }));
    const nItems: OItem[] = newLines.map((t) => ({ text: t, ctx: false }));
    const repl = buildReplacement(oItems, nItems, st.lines, pos, found.tier);
    st.lines.splice(pos, oldLines.length, ...repl);
    tree.now.set(path, serializeFile(st));
  };
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let j = searchIdx - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }
    const oldLines: string[] = [];
    let j = searchIdx + 1;
    let sep = -1;
    while (j < lines.length) {
      if (lines[j]!.trimEnd() === '=======') {
        sep = j;
        break;
      }
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      oldLines.push(lines[j]!);
      j++;
    }
    if (sep < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    const newLines: string[] = [];
    let k = sep + 1;
    let end = -1;
    while (k < lines.length) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
        end = k;
        break;
      }
      if (lines[k]!.trimEnd() === '<<<<<<< SEARCH') break;
      newLines.push(lines[k]!);
      k++;
    }
    if (end < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    edits.push(srEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = end;
    i = end + 1;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

// ---------------------------------------------------------------------------
// Section 8: V4A patches.
// ---------------------------------------------------------------------------

interface VChunk {
  /** The text after `@@`, surrounding spaces removed; null when the chunk has none. */
  anchor: string | null;
  /** True when a `*** End of File` line ended the chunk. */
  eof: boolean;
  items: BodyItem[];
}

interface VSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  headerLine: number;
  items: { text: string; num: number }[];
}

function v4aEdits(lines: string[], strict: boolean, moves: MoveRec[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last--;
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);

  const sections: VSection[] = [];
  let cur: VSection | null = null;
  for (let i = first + 1; i < last; i++) {
    const line = lines[i]!;
    if (blank(line)) {
      if (cur !== null) cur.items.push({ text: line, num: i + 1 });
      continue;
    }
    const isAdd = line.startsWith('*** Add File: ');
    const isDel = line.startsWith('*** Delete File: ');
    const isUpd = line.startsWith('*** Update File: ');
    if (isAdd || isDel || isUpd) {
      const prefix = isAdd ? '*** Add File: ' : isDel ? '*** Delete File: ' : '*** Update File: ';
      cur = {
        kind: isAdd ? 'add' : isDel ? 'delete' : 'update',
        path: line.slice(prefix.length).trim(),
        headerLine: i + 1,
        items: [],
      };
      sections.push(cur);
      continue;
    }
    if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
    cur.items.push({ text: line, num: i + 1 });
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');

  const edits: Edit[] = [];
  for (const s of sections) {
    while (s.items.length > 0 && blank(s.items[s.items.length - 1]!.text)) s.items.pop();
    if (s.kind === 'add') {
      const fileLines: string[] = [];
      for (const it of s.items) {
        if (it.text.startsWith('+')) fileLines.push(it.text.slice(1));
        else if (it.text === '') fileLines.push('');
        else throw new Exit2(`error: parse ${it.num}`);
      }
      const path = s.path;
      const content = fileLines.length === 0 ? '' : fileLines.join('\n') + '\n';
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, content);
      });
      continue;
    }
    if (s.kind === 'delete') {
      for (const it of s.items) {
        if (!blank(it.text)) throw new Exit2(`error: parse ${it.num}`);
      }
      const path = s.path;
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
      continue;
    }
    // Update File: an optional `*** Move to:` first line, then chunks.
    let idx = 0;
    let moveTo: string | null = null;
    if (s.items.length > 0 && s.items[0]!.text.startsWith('*** Move to: ')) {
      moveTo = s.items[0]!.text.slice('*** Move to: '.length).trim();
      idx = 1;
    }
    const chunks: VChunk[] = [];
    let chunk: VChunk | null = null;
    let open = false;
    for (; idx < s.items.length; idx++) {
      const { text, num } = s.items[idx]!;
      if (text.startsWith('@@')) {
        chunk = { anchor: text.slice(2).trim(), eof: false, items: [] };
        chunks.push(chunk);
        open = true;
        continue;
      }
      if (text.trimEnd() === '*** End of File') {
        if (!open || chunk === null) throw new Exit2(`error: parse ${num}`);
        chunk.eof = true;
        open = false;
        continue;
      }
      if (text === '' || text.startsWith(' ') || text.startsWith('-') || text.startsWith('+')) {
        if (!open) {
          if (chunks.length === 0) {
            chunk = { anchor: null, eof: false, items: [] };
            chunks.push(chunk);
            open = true;
          } else {
            throw new Exit2(`error: parse ${num}`);
          }
        }
        chunk!.items.push(bodyItem(text));
        continue;
      }
      throw new Exit2(`error: parse ${num}`);
    }
    if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${s.headerLine}`);
    const path = s.path;
    edits.push((tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
      const before = tree.get(path);
      if (before === null) throw new Fail('missing', path);
      if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
      const st = parseFile(before);
      let cursor = 0;
      for (const ch of chunks) {
        if (ch.anchor !== null && ch.anchor !== '') {
          const at = findAnchorLine(st.lines, ch.anchor, cursor, strict);
          if (at < 0) throw new Fail('no-match', path);
          cursor = at + 1;
        }
        const { o, n } = splitItems(ch.items);
        if (o.length === 0) {
          const insAt = ch.eof ? st.lines.length : cursor;
          const added = n.map((x) => x.text);
          st.lines.splice(insAt, 0, ...added);
          cursor = insAt + added.length;
          continue;
        }
        const found = findTierFrom(st.lines, o.map((x) => x.text), cursor, strict, ch.eof);
        if (found === null) throw new Fail('no-match', path);
        const pos = found.positions[0]!;
        const repl = buildReplacement(o, n, st.lines, pos, found.tier);
        st.lines.splice(pos, o.length, ...repl);
        cursor = pos + repl.length;
      }
      const content = serializeFile(st);
      if (moveTo !== null) {
        tree.now.set(path, null);
        tree.now.set(moveTo, content);
        moves.push({ old: path, new: moveTo });
      } else {
        tree.now.set(path, content);
      }
    });
  }
  return edits;
}

// ---------------------------------------------------------------------------
// Section 4: detecting the format.
// ---------------------------------------------------------------------------

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------------------------------------------------------------------------
// Section 9: JSON edits.
// ---------------------------------------------------------------------------

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------------------------------------------------------------------------
// Sections 1, 2 and 10: the command line, the output and exit codes, and the
// all-or-nothing write. A failed edit changes nothing, and the edits after it
// still run, so every failure is reported. A move that succeeded prints as one
// `R <old> -> <new>` line, sorted by `<new>`, instead of its `D` and `A` lines.
// ---------------------------------------------------------------------------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
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
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const moves: MoveRec[] = [];
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict, moves);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict, moves);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  for (const p of [...tree.now.keys()]) {
    if (tree.original(p) === tree.now.get(p)) continue;
    if (check) continue;
    const now = tree.now.get(p)!;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  interface Row {
    key: string;
    line: string;
  }
  const rows: Row[] = [];
  const suppressed = new Set<string>();
  for (const m of moves) {
    if (tree.original(m.old) !== null && tree.get(m.old) === null && tree.original(m.new) === null && tree.get(m.new) !== null) {
      rows.push({ key: m.new, line: `R ${m.old} -> ${m.new}` });
      suppressed.add(`D ${m.old}`);
      suppressed.add(`A ${m.new}`);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    const k = was === null ? 'A' : now === null ? 'D' : 'M';
    if (suppressed.has(`${k} ${p}`)) continue;
    rows.push({ key: p, line: `${k} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)) || (a.line < b.line ? -1 : a.line > b.line ? 1 : 0));
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
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
