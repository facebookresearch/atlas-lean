/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathEmitSpec
public import CSLibExt.Computability.Complexity.SatCheck
public import CSLibExt.Computability.Complexity.SatLookup
public import Mathlib.Tactic.Ring

/-!
# SAT ≤ HAMPATH, component 2: the emitter machine and its first phase

A `TM2` machine that reads the token stack `(toks φ).reverse` of
`Cslib.Complexity.SatVerifier` and pushes Sipser's HAMPATH instance `toHam φ` onto the output
stack `O`, so that `O` reads the instance top-first.

* Phase A walks the token stack, moving it onto `F` (where it reads `toks φ`), counts the clauses
  on `C` and `3 m` on `M`, and collects the distinct variables on `V`: a name is new when no
  entry of `V` matches it (`cmpB`), and new names are pushed, so `V` lists `hamVars φ` top-first
  (the token stack is read from the end of the formula, and `List.dedup` keeps last occurrences).
  Each entry of `V` is a name block above a `cl` separator.
* The edges are built on `Q` in reading order (`Q` is the reversed reading order) and moved to `O`
  at the end. Diamond `i` (the top entry of `V`) pushes its frame, its row (a `for` loop over `M`)
  and its detours: a walk of `F` onto `T` comparing every literal's name with the entry, with the
  clause's flags in the label, pushing the detour edges at each `cl`; `T` then goes back onto `F`.
  Vertex numbers are unary counters: `P` is the diamond top `hpT m i`, `N` is `hpR m i (3 m)`,
  `R` the current row vertex, `J` the clause, `D` the vertex `hpR m i (3 j + 1)`. A copy site
  (`Site`) pushes a counter in ones and then one or two constant bits.
* Finally the prefix `s`, `t`, `n = t + 1` is pushed onto `O` from `C` and `P`.

This file holds the machine, its quiescent states `MS` (counters in unary, `Q` as the list of
edge bits so far), the copy sites (`site_run`, `chain_run`), the name comparison with restore
(`cmpR_run`) and phase A (`phaseA_run`, ending at `h0` in the state `diaMS`). The diamonds, the
output and the emitter theorem `run` are in `HamPathEmit`. Phase A compares each new name with
every entry of `V`, so it is quadratic in `|toks φ|`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitHam

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability Cslib.Complexity.SatVerifier
open Cslib.Complexity.SatVerifier.Lookup (isBitBlock_map isBitBlock_rev)

/-! ### The machine -/

/-- Stacks: tokens, output, tokens in reading order, distinct variables, the variable walk's
other side, the edges in progress, garbage, comparison scratch (`X`, `Y`), the clause count, three
times it, the diamond top, the row end, the row vertex, the row loop index, the clause index, the
detour vertex, copy scratch. -/
inductive K | T | O | F | V | W | Q | G | X | Y | C | M | P | N | R | L | J | D | Z
  deriving DecidableEq

/-- The stacks, enumerated. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, .O, .F, .V, .W, .Q, .G, .X, .Y, .C, .M, .P, .N, .R, .L, .J, .D, .Z],
    by decide⟩
  complete := fun x => by cases x <;> decide

/-- Stack alphabets: the output stack holds bits, the others token symbols (counters hold
`Sym.cl`). -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- The counters a copy site reads. -/
inductive Src | p | n | r | j | d
  deriving DecidableEq

/-- The stack of a counter. -/
def Src.k : Src → K
  | .p => .P
  | .n => .N
  | .r => .R
  | .j => .J
  | .d => .D

/-- The unit symbol of a counter. -/
def Src.unit : (s : Src) → Γ s.k
  | .p => Sym.cl
  | .n => Sym.cl
  | .r => Sym.cl
  | .j => Sym.cl
  | .d => Sym.cl

/-- Copy sites, two per edge (source and target): the frame (`f`), the row (`w`), the positive
(`d1`, `d2`) and negative (`d3`, `d4`) detours. -/
inductive Site
  | f1u | f1v | f2u | f2v | f3u | f3v | f4u | f4v | w1u | w1v | w2u | w2v
  | d1u | d1v | d2u | d2v | d3u | d3v | d4u | d4v
  deriving DecidableEq

/-- The sites, listed. -/
def Site.all : List Site :=
  [.f1u, .f1v, .f2u, .f2v, .f3u, .f3v, .f4u, .f4v, .w1u, .w1v, .w2u, .w2v,
    .d1u, .d1v, .d2u, .d2v, .d3u, .d3v, .d4u, .d4v]

/-- The sites, enumerated. -/
instance Site.instFintypeEnumFix : Fintype Site :=
  Fintype.ofList Site.all (fun x => by cases x <;> decide)

/-- The counter a site copies. -/
def Site.src : Site → Src
  | .f1u | .f1v | .f2u | .f3u => .p
  | .f2v | .f3v | .f4u | .f4v => .n
  | .w1u | .w1v | .w2u | .w2v => .r
  | .d1u | .d2v | .d3u | .d4v => .d
  | .d1v | .d2u | .d3v | .d4u => .j

/-- The ones a site adds to its counter. -/
def Site.ext : Site → ℕ
  | .f1v | .f3u | .f3v | .f4v | .w1v | .w2u | .d2v | .d3u => 1
  | _ => 0

/-- Labels. Phase A: `a0` reads a token; `anm` moves a name to `F`; `aw f` to `asep f` walk `V`
(`f`: a match was found; `ac` compares, `ar1`, `ar2` restore, `amv`, `asep` move the entry to
`W`); `ab f` moves `W` back (and on no match pushes a separator); `ad2`, `ad3` copy the name onto
`V`. Diamonds: `b0`, `b1` set `P`; `h0` takes the next entry; `h1` to `h5` set `N`; `r0` to `r4`
the row loop (`wi` advances `R`); `e0` to `e2` set `D`; `dw pp pn` walks `F` with the clause flags
(`dk`, `dr1`, `dr2`, `dm`, `dl` handle a literal with match bit `b`; `dj` ends a clause); `t0`
moves `T` back to `F`; `t1` to `t8` drop the entry and advance `P`. `z0` to `z9`: output.
`cpA j b`, `cpB j b`, `post j b`: copy site `j` (`b` is passed on). -/
inductive Lab
  | a0 | anm | aw (f : Bool) | ac (f : Bool) | ar1 (f : Bool) | ar2 (f : Bool) | amv (f : Bool)
  | asep (f : Bool) | ab (f : Bool) | ad2 | ad3
  | b0 | b1 | h0 | h1 | h2 | h3 | h4 | h5 | r0 | r1 | r2 | r3 | r4 | wi | e0 | e1 | e2
  | dw (pp pn : Bool) | dk (pp pn : Bool) | dr1 (pp pn b : Bool) | dr2 (pp pn b : Bool)
  | dm (pp pn b : Bool) | dl (pp pn b : Bool) | dj
  | t0 | t1 | t2 | t3 | t4 | t5 | t6 | t7 | t8
  | z0 | z1 | z2 | z3 | z4 | z5 | z6 | z7 | z8 | z9
  | cpA (j : Site) (b : Bool) | cpB (j : Site) (b : Bool) | post (j : Site) (b : Bool) | done
  deriving DecidableEq

/-- The pairs of booleans. -/
def bb : List (Bool × Bool) := [(true, true), (true, false), (false, true), (false, false)]

/-- The labels, enumerated. -/
instance Lab.instFintypeEnumFix : Fintype Lab :=
  Fintype.ofList
    ([Lab.a0, .anm, .ad2, .ad3, .b0, .b1, .h0, .h1, .h2, .h3, .h4, .h5, .r0, .r1, .r2, .r3,
        .r4, .wi, .e0, .e1, .e2, .dj, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .t7, .t8, .z0, .z1,
        .z2, .z3, .z4, .z5, .z6, .z7, .z8, .z9, .done] ++
      ([true, false].flatMap fun f =>
        [Lab.aw f, .ac f, .ar1 f, .ar2 f, .amv f, .asep f, .ab f]) ++
      (bb.flatMap fun q => [Lab.dw q.1 q.2, .dk q.1 q.2]) ++
      (bb.flatMap fun q => [true, false].flatMap fun b =>
        [Lab.dr1 q.1 q.2 b, .dr2 q.1 q.2 b, .dm q.1 q.2 b, .dl q.1 q.2 b]) ++
      (Site.all.flatMap fun j => [true, false].flatMap fun b =>
        [Lab.cpA j b, .cpB j b, .post j b]))
    (fun x => by
      cases x <;> (try rename_i a b c; cases a <;> cases b <;> cases c) <;>
        (try rename_i a b; cases a <;> cases b) <;> (try rename_i a; cases a) <;> decide)

/-- Where a site continues. -/
def Site.nxt : Site → Bool → Lab
  | .f1u, b => .cpA .f1v b
  | .f1v, b => .cpA .f2u b
  | .f2u, b => .cpA .f2v b
  | .f2v, b => .cpA .f3u b
  | .f3u, b => .cpA .f3v b
  | .f3v, b => .cpA .f4u b
  | .f4u, b => .cpA .f4v b
  | .f4v, _ => .r0
  | .w1u, b => .cpA .w1v b
  | .w1v, b => .cpA .w2u b
  | .w2u, b => .cpA .w2v b
  | .w2v, _ => .wi
  | .d1u, b => .cpA .d1v b
  | .d1v, b => .cpA .d2u b
  | .d2u, b => .cpA .d2v b
  | .d2v, b => if b then .cpA .d3u false else .dj
  | .d3u, b => .cpA .d3v b
  | .d3v, b => .cpA .d4u b
  | .d4u, b => .cpA .d4v b
  | .d4v, _ => .dj

/-- Where the detour walk goes at the end of a clause with flags `pp`, `pn`. -/
def clEnd (pp pn : Bool) : Lab := if pp then .cpA .d1u pn else if pn then .cpA .d3u false else .dj

/-- The machine. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .a0 => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .b0) <|
      .peek .T (fun _ o => o == some .cl) <| .branch id
        (.pop .T (fun s _ => s) <| .push .F (fun _ => Sym.cl) <| .push .C (fun _ => Sym.cl) <|
          pushList .M [Sym.cl, Sym.cl, Sym.cl] <| .goto fun _ => .a0)
        (.pop .T (fun _ o => o == some (.lit true)) <| .push .F (fun s => Sym.lit s) <|
          .goto fun _ => .anm)
  | .anm => moveB .T .F Sym.bit? Sym.bit .anm (.aw false)
  | .aw f => .peek .V (fun _ o => o.isNone) <| .branch id (.goto fun _ => .ab f)
      (.goto fun _ => .ac f)
  | .ac f => cmpB .F .V .X .Y Sym.bit? Sym.bit? Sym.bit Sym.bit (.ac f) (.ar1 true) (.ar1 f)
  | .ar1 f => moveB .X .F Sym.bit? Sym.bit (.ar1 f) (.ar2 f)
  | .ar2 f => moveB .Y .V Sym.bit? Sym.bit (.ar2 f) (.amv f)
  | .amv f => moveB .V .W Sym.bit? Sym.bit (.amv f) (.asep f)
  | .asep f => .pop .V (fun s _ => s) <| .push .W (fun _ => Sym.cl) <| .goto fun _ => .aw f
  | .ab f => .peek .W (fun _ o => o.isNone) <| .branch id
      (if f then .goto fun _ => .a0 else .push .V (fun _ => Sym.cl) <| .goto fun _ => .ad2) <|
      .peek .W (fun _ o => o == some .cl) <| .branch id
        (.pop .W (fun s _ => s) <| .push .V (fun _ => Sym.cl) <| .goto fun _ => .ab f)
        (.pop .W (fun _ o => o == some (.bit true)) <| .push .V (fun s => Sym.bit s) <|
          .goto fun _ => .ab f)
  | .ad2 => moveB .F .X Sym.bit? Sym.bit .ad2 .ad3
  | .ad3 => .peek .X (fun _ o => isBit Sym.bit? o) <| .branch id
      (.pop .X (fun _ o => bitOf Sym.bit? o) <| .push .F (fun s => Sym.bit s) <|
        .push .V (fun s => Sym.bit s) <| .goto fun _ => .ad3)
      (.goto fun _ => .a0)
  | .b0 => xfer .C [⟨.P, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .b0 .b1
  | .b1 => xfer .Z [⟨.C, Sym.cl⟩] .b1 .h0
  | .h0 => .peek .V (fun _ o => o.isNone) <| .branch id (.goto fun _ => .z0)
      (.goto fun _ => .h1)
  | .h1 => xfer .P [⟨.N, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .h1 .h2
  | .h2 => xfer .Z [⟨.P, Sym.cl⟩] .h2 .h3
  | .h3 => xfer .M [⟨.N, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .h3 .h4
  | .h4 => xfer .Z [⟨.M, Sym.cl⟩] .h4 .h5
  | .h5 => .push .N (fun _ => Sym.cl) <| .goto fun _ => .cpA .f1u false
  | .r0 => xfer .P [⟨.R, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .r0 .r1
  | .r1 => xfer .Z [⟨.P, Sym.cl⟩] .r1 .r2
  | .r2 => .push .R (fun _ => Sym.cl) <| .goto fun _ => .r3
  | .r3 => forHead .M .L Sym.cl (.cpA .w1u false) .r4
  | .r4 => xfer .L [⟨.M, Sym.cl⟩] .r4 .e0
  | .wi => .push .R (fun _ => Sym.cl) <| .goto fun _ => .r3
  | .e0 => xfer .P [⟨.D, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .e0 .e1
  | .e1 => xfer .Z [⟨.P, Sym.cl⟩] .e1 .e2
  | .e2 => pushList .D [Sym.cl, Sym.cl] <| .goto fun _ => .dw false false
  | .dw pp pn => .peek .F (fun _ o => o.isNone) <| .branch id (.goto fun _ => .t0) <|
      .peek .F (fun _ o => o == some .cl) <| .branch id
        (.goto fun _ => clEnd pp pn) (.goto fun _ => .dk pp pn)
  | .dk pp pn => cmpB .F .V .X .Y Sym.bit? Sym.bit? Sym.bit Sym.bit (.dk pp pn)
      (.dr1 pp pn true) (.dr1 pp pn false)
  | .dr1 pp pn b => moveB .X .F Sym.bit? Sym.bit (.dr1 pp pn b) (.dr2 pp pn b)
  | .dr2 pp pn b => moveB .Y .V Sym.bit? Sym.bit (.dr2 pp pn b) (.dm pp pn b)
  | .dm pp pn b => moveB .F .T Sym.bit? Sym.bit (.dm pp pn b) (.dl pp pn b)
  | .dl pp pn b => .pop .F (fun _ o => o == some (.lit true)) <|
      .push .T (fun s => Sym.lit s) <| .goto fun s => .dw (pp || (b && s)) (pn || (b && !s))
  | .dj => .pop .F (fun s _ => s) <| .push .T (fun _ => Sym.cl) <|
      .push .J (fun _ => Sym.cl) <| pushList .D [Sym.cl, Sym.cl, Sym.cl] <|
        .goto fun _ => .dw false false
  | .t0 => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .t1) <|
      .peek .T (fun _ o => o == some .cl) <| .branch id
        (.pop .T (fun s _ => s) <| .push .F (fun _ => Sym.cl) <| .goto fun _ => .t0) <|
      .peek .T (fun _ o => isBit Sym.bit? o) <| .branch id
        (.pop .T (fun _ o => bitOf Sym.bit? o) <| .push .F (fun s => Sym.bit s) <|
          .goto fun _ => .t0)
        (.pop .T (fun _ o => o == some (.lit true)) <| .push .F (fun s => Sym.lit s) <|
          .goto fun _ => .t0)
  | .t1 => moveB .V .G Sym.bit? Sym.bit .t1 .t2
  | .t2 => .pop .V (fun s _ => s) <| .goto fun _ => .t3
  | .t3 => xfer .P [] .t3 .t4
  | .t4 => xfer .N [⟨.P, Sym.cl⟩] .t4 .t5
  | .t5 => .push .P (fun _ => Sym.cl) <| .goto fun _ => .t6
  | .t6 => xfer .R [] .t6 .t7
  | .t7 => xfer .J [] .t7 .t8
  | .t8 => xfer .D [] .t8 .h0
  | .z0 => moveB .Q .O Sym.bit? id .z0 .z1
  | .z1 => pushList .O [false, true] <| .goto fun _ => .z2
  | .z2 => xfer .P [⟨.O, true⟩, ⟨.Z, Sym.cl⟩] .z2 .z3
  | .z3 => xfer .Z [⟨.P, Sym.cl⟩] .z3 .z4
  | .z4 => .push .O (fun _ => false) <| .goto fun _ => .z5
  | .z5 => xfer .P [⟨.O, true⟩, ⟨.Z, Sym.cl⟩] .z5 .z6
  | .z6 => xfer .Z [⟨.P, Sym.cl⟩] .z6 .z7
  | .z7 => .push .O (fun _ => false) <| .goto fun _ => .z8
  | .z8 => xfer .C [⟨.O, true⟩, ⟨.Z, Sym.cl⟩] .z8 .z9
  | .z9 => xfer .Z [⟨.C, Sym.cl⟩] .z9 .done
  | .cpA j b => xfer j.src.k [⟨.Q, Sym.bit true⟩, ⟨.Z, Sym.cl⟩] (.cpA j b) (.cpB j b)
  | .cpB j b => xfer .Z [⟨j.src.k, j.src.unit⟩] (.cpB j b) (.post j b)
  | .post j b => emit .Q ((List.replicate j.ext true ++ [false]).map Sym.bit) (j.nxt b)
  | .done => .halt

/-- The start label. -/
def start : Lab := .a0

/-! ### Quiescent states -/

/-- A quiescent state: counters are unary stacks of `Sym.cl`, `Q` holds the edge bits `q` (in
reading order, so reversed on the stack), and the scratch stacks `Y`, `Z` are empty (`X` is
empty except while a new name is copied onto `V`). -/
structure MS where
  /-- The token stack. -/
  t : List Sym
  /-- The output stack. -/
  o : List Bool
  /-- The tokens in reading order. -/
  f : List Sym
  /-- The distinct variables. -/
  v : List Sym
  /-- The variable walk's other side. -/
  w : List Sym
  /-- The edge bits so far, in reading order. -/
  q : List Bool
  /-- Garbage. -/
  g : List Sym
  /-- The first comparison scratch stack. -/
  x : List Sym
  /-- The clause count. -/
  c : ℕ
  /-- Three times the clause count. -/
  mm : ℕ
  /-- The diamond top. -/
  p : ℕ
  /-- The row end. -/
  n : ℕ
  /-- The row vertex. -/
  r : ℕ
  /-- The row loop index. -/
  l : ℕ
  /-- The clause index. -/
  j : ℕ
  /-- The detour vertex. -/
  d : ℕ

/-- The stacks of a quiescent state. -/
def MS.stk (s : MS) : ∀ k, List (Γ k)
  | .T => s.t
  | .O => s.o
  | .F => s.f
  | .V => s.v
  | .W => s.w
  | .Q => s.q.reverse.map Sym.bit
  | .G => s.g
  | .C => cnt Sym.cl s.c
  | .M => cnt Sym.cl s.mm
  | .P => cnt Sym.cl s.p
  | .N => cnt Sym.cl s.n
  | .R => cnt Sym.cl s.r
  | .L => cnt Sym.cl s.l
  | .J => cnt Sym.cl s.j
  | .D => cnt Sym.cl s.d
  | .X => s.x
  | .Y | .Z => []

/-- The value of a counter. -/
def MS.val (s : MS) : Src → ℕ
  | .p => s.p
  | .n => s.n
  | .r => s.r
  | .j => s.j
  | .d => s.d

section MSLemmas

variable (s : MS)

@[simp] theorem stk_T : s.stk .T = s.t := rfl
@[simp] theorem stk_O : s.stk .O = s.o := rfl
@[simp] theorem stk_F : s.stk .F = s.f := rfl
@[simp] theorem stk_V : s.stk .V = s.v := rfl
@[simp] theorem stk_W : s.stk .W = s.w := rfl
@[simp] theorem stk_Q : s.stk .Q = s.q.reverse.map Sym.bit := rfl
@[simp] theorem stk_G : s.stk .G = s.g := rfl
@[simp] theorem stk_C : s.stk .C = List.replicate s.c Sym.cl := rfl
@[simp] theorem stk_M : s.stk .M = List.replicate s.mm Sym.cl := rfl
@[simp] theorem stk_P : s.stk .P = List.replicate s.p Sym.cl := rfl
@[simp] theorem stk_N : s.stk .N = List.replicate s.n Sym.cl := rfl
@[simp] theorem stk_R : s.stk .R = List.replicate s.r Sym.cl := rfl
@[simp] theorem stk_L : s.stk .L = List.replicate s.l Sym.cl := rfl
@[simp] theorem stk_J : s.stk .J = List.replicate s.j Sym.cl := rfl
@[simp] theorem stk_D : s.stk .D = List.replicate s.d Sym.cl := rfl
@[simp] theorem stk_X : s.stk .X = s.x := rfl
@[simp] theorem stk_Y : s.stk .Y = [] := rfl
@[simp] theorem stk_Z : s.stk .Z = [] := rfl

@[simp] theorem upd_T (x : List Sym) : update s.stk .T x = {s with t := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_O (x : List Bool) : update s.stk .O x = {s with o := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_F (x : List Sym) : update s.stk .F x = {s with f := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_V (x : List Sym) : update s.stk .V x = {s with v := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_W (x : List Sym) : update s.stk .W x = {s with w := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_G (x : List Sym) : update s.stk .G x = {s with g := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_X (y : List Sym) : update s.stk .X y = {s with x := y}.stk := by
  funext k; cases k <;> rfl
theorem upd_Q (q : List Bool) :
    update s.stk .Q (q.reverse.map Sym.bit) = {s with q := q}.stk := by
  funext k; cases k <;> rfl
theorem upd_C (x : ℕ) : update s.stk .C (cnt Sym.cl x) = {s with c := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_M (x : ℕ) : update s.stk .M (cnt Sym.cl x) = {s with mm := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_P (x : ℕ) : update s.stk .P (cnt Sym.cl x) = {s with p := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_N (x : ℕ) : update s.stk .N (cnt Sym.cl x) = {s with n := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_R (x : ℕ) : update s.stk .R (cnt Sym.cl x) = {s with r := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_L (x : ℕ) : update s.stk .L (cnt Sym.cl x) = {s with l := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_J (x : ℕ) : update s.stk .J (cnt Sym.cl x) = {s with j := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_D (x : ℕ) : update s.stk .D (cnt Sym.cl x) = {s with d := x}.stk := by
  funext k; cases k <;> rfl

theorem stk_src (u : Src) : s.stk u.k = cnt u.unit (s.val u) := by cases u <;> rfl

end MSLemmas

@[simp] theorem sym_beq (a b : Sym) : (a == b) = decide (a = b) := rfl

theorem runLe_cast {k k' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog k c d)
    (hk : k ≤ k') (hd : d = d') : RunLe prog k' c d' := hd ▸ h.mono hk

/-! ### Copies and copy sites -/

/-- Copy counter `a` onto stack `c`, one `x` per unit, restoring it through `Z`: `2 val + 2`
steps. -/
theorem cp_run {a c : K} (ua : Γ a) (x : Γ c) (hca : c ≠ a) (haZ : a ≠ .Z) (hcZ : c ≠ .Z)
    {l₁ l₂ next : Lab} (h₁ : prog l₁ = xfer a [⟨c, x⟩, ⟨.Z, Sym.cl⟩] l₁ l₂)
    (h₂ : prog l₂ = xfer .Z [⟨a, ua⟩] l₂ next) (val : ℕ) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : S a = cnt ua val) (hZ : S .Z = []) :
    ∃ v', Run prog (2 * val + 2) ⟨some l₁, v, S⟩
      ⟨some next, v', update S c (cnt x val ++ S c)⟩ := by
  have r₁ := xfer_run h₁ (pair_nodupKeys x (Sym.cl : Γ .Z) hcZ) (by simp [hca.symm, haZ]) ua
    val v S hS
  set S₁ := addU [⟨c, x⟩, ⟨.Z, Sym.cl⟩] val (update S a []) with hS₁
  have h₁Z : S₁ .Z = cnt (Sym.cl : Γ .Z) val := by
    rw [hS₁, addU_pair_snd _ _ _ _ hcZ.symm, update_of_ne haZ.symm, hZ, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys ua) (by simp [haZ.symm]) (Sym.cl : Γ .Z) val
    (Flag.tag false) S₁ h₁Z
  have hfin : addU [⟨a, ua⟩] val (update S₁ .Z []) = update S c (cnt x val ++ S c) := by
    funext k
    by_cases hka : k = a
    · subst hka
      rw [addU_single_self, update_of_ne haZ, hS₁, addU_pair_ne _ _ _ _ hca.symm haZ,
        update_self, update_of_ne hca.symm, hS, List.append_nil]
    rw [addU_single_ne _ _ _ hka]
    by_cases hkZ : k = .Z
    · subst hkZ; rw [update_self, update_of_ne hcZ.symm, hZ]
    rw [update_of_ne hkZ]
    by_cases hkc : k = c
    · subst hkc; rw [hS₁, addU_pair_fst, update_of_ne hca, update_self]
    rw [hS₁, addU_pair_ne _ _ _ _ hkc hkZ, update_of_ne hka, update_of_ne hkc]
  rw [hfin] at r₂
  exact ⟨_, (r₁.trans r₂).of_eq (by omega)⟩

theorem Src.k_ne_Q (u : Src) : u.k ≠ .Q := by cases u <;> decide

theorem Src.k_ne_Z (u : Src) : u.k ≠ .Z := by cases u <;> decide

/-- The bits site `j` pushes: its counter plus its extra ones, in ones, then `false`. -/
def atom (s : MS) (j : Site) : List Bool := List.replicate (s.val j.src + j.ext) true ++ [false]

theorem q_push (q x : List Bool) (e : ℕ) :
    ((List.replicate e true ++ [false]).map Sym.bit).reverse ++
      (cnt (Sym.bit true) x.length ++ q.reverse.map Sym.bit) =
      (q ++ (List.replicate (x.length + e) true ++ [false])).reverse.map Sym.bit := by
  rw [Nat.add_comm]
  simp [List.map_reverse, List.reverse_append, cnt, ← List.append_assoc]

/-- A copy site: from `cpA j b`, append `atom s j` to the edge bits and continue at `j.nxt b`. -/
theorem site_run (j : Site) (b : Bool) (s : MS) (v : Bool) :
    ∃ v', Run prog (2 * s.val j.src + 3) ⟨some (.cpA j b), v, s.stk⟩
      ⟨some (j.nxt b), v', {s with q := s.q ++ atom s j}.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := cp_run (a := j.src.k) (c := .Q) j.src.unit (Sym.bit true)
    (Ne.symm j.src.k_ne_Q) j.src.k_ne_Z (by decide) (l₁ := .cpA j b) (l₂ := .cpB j b)
    (next := .post j b) rfl rfl (s.val j.src) v s.stk (stk_src s j.src) rfl
  have r₂ := emit_run (M := prog) (self := .post j b) (next := j.nxt b) (k := .Q)
    (xs := (List.replicate j.ext true ++ [false]).map Sym.bit) rfl v₁
    (update s.stk .Q (cnt (Sym.bit true) (s.val j.src) ++ s.stk .Q))
  have e : update (update s.stk .Q (cnt (Sym.bit true) (s.val j.src) ++ s.stk .Q)) .Q
      (((List.replicate j.ext true ++ [false]).map Sym.bit).reverse ++
        update s.stk .Q (cnt (Sym.bit true) (s.val j.src) ++ s.stk .Q) .Q) =
      {s with q := s.q ++ atom s j}.stk := by
    rw [update_idem, update_self, stk_Q]
    have := q_push s.q (List.replicate (s.val j.src) true) j.ext
    rw [List.length_replicate] at this
    rw [this, upd_Q]
    rfl
  rw [e] at r₂
  exact ⟨v₁, (r₁.trans r₂).of_eq (by omega)⟩

/-- The sites `js` run in sequence from label `l₀` with the passed bit `b`, the last one
continuing at `l`. -/
def Chain : List Site → Bool → Lab → Lab → Bool
  | [], _, l₀, l => l₀ == l
  | j :: js, b, l₀, l => l₀ == .cpA j b && Chain js b (j.nxt b) l

/-- The steps of a run of sites. -/
def chainCost (s : MS) (js : List Site) : ℕ := (js.map fun j => 2 * s.val j.src + 3).sum

theorem atom_q (s : MS) (x : List Bool) : atom {s with q := x} = atom s := by
  funext j'; simp only [atom]; cases j'.src <;> rfl

theorem chainCost_q (s : MS) (x : List Bool) (js : List Site) :
    chainCost {s with q := x} js = chainCost s js := by
  simp only [chainCost]; congr 1

theorem chainCost_le (s : MS) (Bd : ℕ) (hB : ∀ u, s.val u ≤ Bd) (js : List Site) :
    chainCost s js ≤ js.length * (2 * Bd + 3) := by
  induction js with
  | nil => simp [chainCost]
  | cons j js ih =>
      have := hB j.src
      simp only [chainCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      nlinarith

/-- A run of sites appends the atoms of its sites. -/
theorem chain_run (js : List Site) : ∀ (s : MS) (b : Bool) (l₀ l : Lab),
    Chain js b l₀ l = true → ∀ v : Bool, ∃ v', Run prog (chainCost s js) ⟨some l₀, v, s.stk⟩
      ⟨some l, v', {s with q := s.q ++ (js.map (atom s)).flatten}.stk⟩ := by
  induction js with
  | nil =>
      intro s b l₀ l h v
      simp only [Chain, beq_iff_eq] at h
      subst h
      exact ⟨v, by simpa [chainCost] using Run.zero (M := prog) _⟩
  | cons j js ih =>
      intro s b l₀ l h v
      simp only [Chain, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨v₁, r₁⟩ := site_run j b s v
      obtain ⟨v₂, r₂⟩ := ih {s with q := s.q ++ atom s j} b (j.nxt b) l h v₁
      rw [chainCost_q] at r₂
      have e : chainCost s (j :: js) = 2 * s.val j.src + 3 + chainCost s js := by
        simp [chainCost]
      rw [e]
      have r := r₁.trans r₂
      simp only [atom_q, List.append_assoc] at r
      exact ⟨v₂, by simpa using r⟩

/-! ### Comparing a name on `F` with the top entry of `V` -/

theorem bit_inv (x : Sym) (b : Bool) (h : Sym.bit? x = some b) : Sym.bit b = x := by
  cases x <;> simp_all [Sym.bit?]

/-- Compare the name block `u` on `F` with the block `w` on `V` and restore both; continue at
`nx bT` on a match, `nx bF` otherwise. -/
theorem cmpR_run {lc : Lab} {r1 r2 nx : Bool → Lab} {bT bF : Bool}
    (hc : prog lc = cmpB .F .V .X .Y Sym.bit? Sym.bit? Sym.bit Sym.bit lc (r1 bT) (r1 bF))
    (h1 : ∀ b, prog (r1 b) = moveB .X .F Sym.bit? Sym.bit (r1 b) (r2 b))
    (h2 : ∀ b, prog (r2 b) = moveB .Y .V Sym.bit? Sym.bit (r2 b) (nx b))
    (s : MS) (v : Bool) (u w : List Bool) (A B : List Sym) (hA : A.head?.bind Sym.bit? = none)
    (hB : B.head?.bind Sym.bit? = none) (hf : s.f = u.map Sym.bit ++ A)
    (hv : s.v = w.map Sym.bit ++ B) (hx : s.x = []) :
    ∃ v', RunLe prog (3 * w.length + 3) ⟨some lc, v, s.stk⟩
      ⟨some (nx (if u = w then bT else bF)), v', s.stk⟩ := by
  have hd : Distinct4 K.F K.V K.X K.Y :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨cp, v₁, S₁, hcu, hcw, -, r₁, h1F, h1V, h1X, h1Y, h1k⟩ := cmpB_run (M := prog)
    (self := lc) (eqL := r1 bT) (neL := r1 bF) (a := .F) (b := .V)
    (ta := .X) (tb := .Y) (da := Sym.bit?) (db := Sym.bit?) (ea := Sym.bit) (eb := Sym.bit) hc
    hd u w (u.map Sym.bit) A (w.map Sym.bit) B v s.stk (by simp [hf]) (by simp [hv])
    (isBitBlock_map u) (isBitBlock_map w) hA hB
  set b := if u = w then bT else bF with hb
  have hl : (if u = w then r1 bT else r1 bF) = r1 b := by rw [hb]; split <;> rfl
  rw [hl] at r₁
  obtain ⟨v₂, S₂, r₂, h2X, h2F, h2k⟩ := moveB_restore (M := prog) (self' := r1 b)
    (next := r2 b) (t := .X) (a := .F) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) (h1 b) (by decide) (fun _ => rfl) bit_inv u cp (u.map Sym.bit) A [] v₁ S₁
    (isBitBlock_map u) hcu (by simp [h1X, hx]) (by simp [h1F]) rfl
  obtain ⟨v₃, S₃, r₃, h3Y, h3V, h3k⟩ := moveB_restore (M := prog) (self' := r2 b)
    (next := nx b) (t := .Y) (a := .V) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) (h2 b) (by decide) (fun _ => rfl) bit_inv w cp (w.map Sym.bit) B [] v₂ S₂
    (isBitBlock_map w) hcw (by simp [h2k, h1Y]) (by simp [h2k, h1V]) rfl
  have hS : S₃ = s.stk := by
    funext k; cases k <;> simp [h3Y, h3V, h3k, h2X, h2F, h2k, h1k, hf, hv, hx]
  rw [hS] at r₃
  refine ⟨v₃, ((r₁.trans r₂).trans r₃).le ?_⟩
  have := hcw.length_le
  omega

/-! ### Phase A: tokens to `F`, clause counts, distinct variables -/

/-- The name bits of variable `x`. -/
abbrev name (x : ℕ) : List Sym := (encodeNat x).map Sym.bit

/-- The variable stack: each name above a `cl` separator. -/
def vstk (vs : List ℕ) : List Sym := vs.flatMap fun x => name x ++ [Sym.cl]

/-- Symbols of the variable stack. -/
def isVS : Sym → Bool
  | .bit _ | .cl => true
  | _ => false

theorem isVS_vstk (vs : List ℕ) : ∀ x ∈ vstk vs, isVS x = true := by
  intro x hx
  simp only [vstk, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton] at hx
  obtain ⟨_, -, ⟨b, -, rfl⟩ | rfl⟩ := hx <;> rfl

section PhaseA

variable (s : MS) (v : Bool)

theorem a0_nil (h : s.t = []) : Run prog 1 ⟨some .a0, v, s.stk⟩ ⟨some .b0, true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem a0_cl (R : List Sym) (h : s.t = .cl :: R) : Run prog 1 ⟨some .a0, v, s.stk⟩
    ⟨some .a0, true, {s with t := R, f := .cl :: s.f, c := s.c + 1, mm := s.mm + 3}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_T, h, List.head?_cons, Option.isNone_some, id_eq, BEq.rfl,
      List.tail_cons, upd_T, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, stk_F, upd_F,
      stk_C, stepAux_pushList, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, stk_M, Option.some_beq_some, sym_beq, decide_false, cond_eq_ite,
      ↓reduceIte, Bool.false_eq_true, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

theorem a0_lit (p : Bool) (R : List Sym) (h : s.t = .lit p :: R) :
    Run prog 1 ⟨some .a0, v, s.stk⟩ ⟨some .anm, p, {s with t := R, f := .lit p :: s.f}.stk⟩ :=
  Run.single (by cases p <;> simp [prog, TM2.stepAux, h])

theorem aw_nil (f : Bool) (h : s.v = []) :
    Run prog 1 ⟨some (.aw f), v, s.stk⟩ ⟨some (.ab f), true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem aw_cons (f : Bool) (x : Sym) (R : List Sym) (h : s.v = x :: R) :
    Run prog 1 ⟨some (.aw f), v, s.stk⟩ ⟨some (.ac f), false, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem asep_step (f : Bool) (R : List Sym) (h : s.v = .cl :: R) :
    Run prog 1 ⟨some (.asep f), v, s.stk⟩ ⟨some (.aw f), v, {s with v := R, w := .cl :: s.w}.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem ab_nil_true (h : s.w = []) :
    Run prog 1 ⟨some (.ab true), v, s.stk⟩ ⟨some .a0, true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem ab_nil_false (h : s.w = []) :
    Run prog 1 ⟨some (.ab false), v, s.stk⟩ ⟨some .ad2, true, {s with v := .cl :: s.v}.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem ab_step (f : Bool) (x : Sym) (hx : isVS x = true) (R : List Sym) (h : s.w = x :: R) :
    ∃ v', Run prog 1 ⟨some (.ab f), v, s.stk⟩
      ⟨some (.ab f), v', {s with w := R, v := x :: s.v}.stk⟩ := by
  cases x with
  | bit b => exact ⟨b, Run.single (by cases b <;> simp [prog, TM2.stepAux, h])⟩
  | cl => exact ⟨true, Run.single (by simp [prog, TM2.stepAux, h])⟩
  | _ => simp [isVS] at hx

end PhaseA

/-- Move `W` back onto `V`. -/
theorem ab_run (f : Bool) : ∀ (L : List Sym), (∀ x ∈ L, isVS x = true) → ∀ (s : MS) (v : Bool),
    s.w = L → ∃ v', Run prog L.length ⟨some (.ab f), v, s.stk⟩
      ⟨some (.ab f), v', {s with w := [], v := L.reverse ++ s.v}.stk⟩ := by
  intro L
  induction L with
  | nil =>
      intro _ s v h
      have e : ({s with w := [], v := ([] : List Sym).reverse ++ s.v} : MS) = s := by
        cases s; simp_all
      exact ⟨v, by rw [e]; exact Run.zero _⟩
  | cons x L ih =>
      intro hL s v h
      obtain ⟨v₁, r₁⟩ := ab_step s v f x (hL x (by simp)) L h
      obtain ⟨v₂, r₂⟩ := ih (fun y hy => hL y (by simp [hy])) {s with w := L, v := x :: s.v} v₁
        rfl
      exact ⟨v₂, by simpa [Nat.add_comm] using r₁.trans r₂⟩

/-- Walk the variable stack `vstk vs`, comparing each entry with the name `x` on top of `F`;
the flag ends as `f || x ∈ vs` and `V` ends on `W`, reversed. -/
theorem aw_run (x : ℕ) (A : List Sym) (hA : A.head?.bind Sym.bit? = none) :
    ∀ (vs : List ℕ) (f : Bool) (s : MS) (v : Bool), s.f = name x ++ A → s.v = vstk vs →
      s.x = [] →
      ∃ v', RunLe prog (6 * (vstk vs).length + 1) ⟨some (.aw f), v, s.stk⟩
        ⟨some (.ab (f || decide (x ∈ vs))), v',
          {s with v := [], w := (vstk vs).reverse ++ s.w}.stk⟩ := by
  intro vs
  induction vs with
  | nil =>
      intro f s v _ hv _
      have e : ({s with v := [], w := (vstk []).reverse ++ s.w} : MS) = s := by
        cases s; simp_all [vstk]
      exact ⟨true, runLe_cast ((aw_nil s v f hv).le le_rfl) (by simp) (by simp [e])⟩
  | cons y vs ih =>
      intro f s v hf hv hx
      have hv' : s.v = name y ++ Sym.cl :: vstk vs := by simp [hv, vstk]
      obtain ⟨x0, R0, hx0⟩ : ∃ x0 R0, s.v = x0 :: R0 := by
        rw [hv']
        cases h : encodeNat y with
        | nil => exact ⟨Sym.cl, vstk vs, by simp [name, h]⟩
        | cons b t => exact ⟨Sym.bit b, t.map Sym.bit ++ Sym.cl :: vstk vs, by simp [name, h]⟩
      have r₁ := aw_cons s v f x0 R0 hx0
      obtain ⟨v₂, r₂⟩ := cmpR_run (lc := .ac f) (r1 := .ar1) (r2 := .ar2) (nx := .amv)
        (bT := true) (bF := f) rfl (fun _ => rfl) (fun _ => rfl) s false (encodeNat x)
        (encodeNat y) A (Sym.cl :: vstk vs) hA rfl hf hv' hx
      set f' := if encodeNat x = encodeNat y then true else f with hf'
      obtain ⟨v₃, S₃, r₃, h3V, h3W, h3k⟩ := moveB_run (M := prog) (self := .amv f')
        (next := .asep f') (a := .V) (b := .W) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
        (encodeNat y) (name y) (Sym.cl :: vstk vs) v₂ s.stk (by simp [hv'])
        (isBitBlock_map _) rfl
      have hS₃ : S₃ = {s with v := Sym.cl :: vstk vs, w := (name y).reverse ++ s.w}.stk := by
        funext k; cases k <;> simp [h3V, h3W, h3k]
      rw [hS₃] at r₃
      have r₄ := asep_step {s with v := Sym.cl :: vstk vs, w := (name y).reverse ++ s.w} v₃ f'
        (vstk vs) rfl
      obtain ⟨v₅, r₅⟩ := ih f' {s with v := vstk vs, w := Sym.cl :: ((name y).reverse ++ s.w)}
        v₃ hf rfl hx
      have hff : (f' || decide (x ∈ vs)) = (f || decide (x ∈ y :: vs)) := by
        rw [hf']
        by_cases hxy : x = y
        · subst hxy; simp
        · have : encodeNat x ≠ encodeNat y := fun h => hxy (encodeNat_inj.1 h)
          simp [this, hxy]
      rw [hff] at r₅
      refine ⟨v₅, runLe_cast ((r₁.le le_rfl).trans (r₂.trans (((r₃.trans r₄).le le_rfl).trans
        r₅))) ?_ ?_⟩
      · simp [vstk]; omega
      · simp [vstk, List.reverse_append]

/-- Copy the reversed name on `X` onto `F` and `V`. -/
theorem ad3_run : ∀ (u : List Bool) (s : MS) (v : Bool), s.x = u.map Sym.bit →
    ∃ v', Run prog (u.length + 1) ⟨some .ad3, v, s.stk⟩ ⟨some .a0, v',
      { s with
        x := [], f := (u.map Sym.bit).reverse ++ s.f, v := (u.map Sym.bit).reverse ++ s.v }.stk⟩ :=
    by
  intro u
  induction u with
  | nil =>
      intro s v h
      have e : ({ s with
          x := [], f := (([] : List Bool).map Sym.bit).reverse ++ s.f,
          v := (([] : List Bool).map Sym.bit).reverse ++ s.v } : MS) = s := by
        cases s; simp_all
      exact ⟨false, by rw [e]; exact Run.single (by simp [prog, TM2.stepAux, h, isBit])⟩
  | cons b u ih =>
      intro s v h
      have r₁ : Run prog 1 ⟨some .ad3, v, s.stk⟩ ⟨some .ad3, b,
          { s with x := u.map Sym.bit, f := Sym.bit b :: s.f, v := Sym.bit b :: s.v }.stk⟩ :=
        Run.single (by cases b <;> simp [prog, TM2.stepAux, h, isBit, bitOf, Sym.bit?])
      obtain ⟨v₂, r₂⟩ := ih { s with
        x := u.map Sym.bit, f := Sym.bit b :: s.f, v := Sym.bit b :: s.v } b rfl
      have e : ({ ({ s with x := u.map Sym.bit, f := Sym.bit b :: s.f, v := Sym.bit b :: s.v } : MS)
          with
          x := [], f := (u.map Sym.bit).reverse ++ (Sym.bit b :: s.f),
          v := (u.map Sym.bit).reverse ++ (Sym.bit b :: s.v) } : MS) =
          { s with
            x := [], f := ((b :: u).map Sym.bit).reverse ++ s.f,
            v := ((b :: u).map Sym.bit).reverse ++ s.v } := by simp
      rw [e] at r₂
      exact ⟨v₂, (r₁.trans r₂).of_eq (by simp; omega)⟩

theorem vstk_insV_le (x : ℕ) (vs : List ℕ) :
    (vstk (insV x vs)).length ≤ (vstk vs).length + (encodeNat x).length + 1 := by
  unfold insV; split <;> simp [vstk] <;> omega

theorem vstk_lits_le (Ls : List (ℕ × Bool)) (vs : List ℕ) :
    (vstk (Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs)).length ≤
      (vstk vs).length + (Ls.flatMap Check.litRev).length := by
  induction Ls with
  | nil => simp
  | cons l' Ls ih' =>
      have := vstk_insV_le l'.1 (Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs)
      have := Check.litRev_length l'
      simp only [List.foldr_cons, List.flatMap_cons, List.length_append] at this ih' ⊢
      omega

/-- One literal of phase A: its tokens go to `F`, and its variable onto `V` if new. -/
theorem alit_run (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (vs : List ℕ) (s : MS) (v : Bool) (ht : s.t = Check.litRev l ++ R) (hv : s.v = vstk vs)
    (hw : s.w = []) (hx : s.x = []) :
    ∃ v', RunLe prog (8 * (vstk vs).length + 4 * (Check.litRev l).length + 8)
      ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', {s with t := R, f := litToks l ++ s.f, v := vstk (insV l.1 vs)}.stk⟩ := by
  obtain ⟨x, p⟩ := l
  have hlen : (Check.litRev (x, p)).length = (encodeNat x).length + 1 := Check.litRev_length _
  have r₁ := a0_lit s v p ((name x).reverse ++ R) (by simp [ht, Check.litRev])
  set s₁ := {s with t := (name x).reverse ++ R, f := Sym.lit p :: s.f}
  obtain ⟨v₂, S₂, r₂, h2T, h2F, h2k⟩ := moveB_run (M := prog) (self := .anm)
    (next := .aw false) (a := .T) (b := .F) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
    (encodeNat x).reverse (name x).reverse R p s₁.stk rfl (isBitBlock_rev _) hR
  have hS₂ : S₂ = {s₁ with t := R, f := name x ++ Sym.lit p :: s.f}.stk := by
    funext k; cases k <;> simp [h2T, h2F, h2k, s₁, List.map_reverse]
  rw [hS₂] at r₂
  set s₂ := {s₁ with t := R, f := name x ++ Sym.lit p :: s.f}
  obtain ⟨v₃, r₃⟩ := aw_run x (Sym.lit p :: s.f) rfl vs false s₂ v₂ rfl (by simp [s₂, s₁, hv])
    (by simp [s₂, s₁, hx])
  obtain ⟨v₄, r₄⟩ := ab_run (false || decide (x ∈ vs)) ((vstk vs).reverse ++ s₂.w)
    (fun y hy => by
      simp only [s₂, s₁, hw, List.append_nil, List.mem_reverse] at hy
      exact isVS_vstk vs y hy)
    {s₂ with v := [], w := (vstk vs).reverse ++ s₂.w} v₃ rfl
  set s₄ : MS := {s₂ with w := [], v := ((vstk vs).reverse ++ s₂.w).reverse ++ []} with hs₄
  have hs₄v : s₄.v = vstk vs := by simp [s₄, s₂, s₁, hw]
  have hlt : litToks (x, p) = name x ++ [Sym.lit p] := rfl
  by_cases hm : x ∈ vs
  · have r₅ := ab_nil_true s₄ v₄ rfl
    simp only [hm, decide_true, Bool.false_or] at r₃ r₄
    refine ⟨true, runLe_cast ((r₁.trans r₂).le le_rfl |>.trans
      (r₃.trans ((r₄.trans r₅).le le_rfl))) ?_ ?_⟩
    · simp [s₂, s₁, hw]; omega
    · congr 2
      simp [s₄, s₂, s₁, hlt, insV, hm, hw, hx]
  · have r₅ := ab_nil_false s₄ v₄ rfl
    simp only [hm, decide_false, Bool.false_or] at r₃ r₄
    set s₅ := {s₄ with v := Sym.cl :: s₄.v}
    obtain ⟨v₆, S₆, r₆, h6F, h6X, h6k⟩ := moveB_run (M := prog) (self := .ad2)
      (next := .ad3) (a := .F) (b := .X) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      (encodeNat x) (name x) (Sym.lit p :: s.f) true s₅.stk (by simp [s₅, s₄, s₂])
      (isBitBlock_map _) rfl
    have hS₆ : S₆ = {s₅ with f := Sym.lit p :: s.f, x := (name x).reverse}.stk := by
      funext k; cases k <;> simp [h6F, h6X, h6k, s₅, s₄, s₂, s₁, hx]
    rw [hS₆] at r₆
    obtain ⟨v₇, r₇⟩ := ad3_run (encodeNat x).reverse
      {s₅ with f := Sym.lit p :: s.f, x := (name x).reverse} v₆ (by simp [List.map_reverse])
    refine ⟨v₇, runLe_cast ((r₁.trans r₂).le le_rfl |>.trans
      (r₃.trans ((((r₄.trans r₅).trans r₆).trans r₇).le le_rfl))) ?_ ?_⟩
    · simp [s₂, s₁, hw]; omega
    · congr 2
      simp [s₅, s₄, s₂, s₁, hlt, insV, hm, hw, hx, vstk, List.map_reverse]

/-- The literals of a clause, met last-first: their tokens go to `F` and their variables onto
`V`. -/
theorem alits_run (Lb : ℕ) : ∀ (Ls : List (ℕ × Bool)) (R : List Sym),
    R.head?.bind Sym.bit? = none → ∀ (vs : List ℕ) (s : MS) (v : Bool),
    s.t = Ls.reverse.flatMap Check.litRev ++ R → s.v = vstk vs → s.w = [] → s.x = [] →
    (vstk vs).length + (Ls.flatMap Check.litRev).length ≤ Lb →
    ∃ v', RunLe prog ((Ls.flatMap Check.litRev).length * (8 * Lb + 12)) ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', { s with
        t := R, f := Ls.flatMap litToks ++ s.f,
        v := vstk (Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs) }.stk⟩ := by
  intro Ls
  induction Ls with
  | nil =>
      intro R _ vs s v ht hv _ _ _
      have e : ({ s with
          t := R, f := ([] : List (ℕ × Bool)).flatMap litToks ++ s.f,
          v := vstk (([] : List (ℕ × Bool)).foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs) } :
          MS) = s := by
        cases s; simp_all
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by rw [e])⟩
  | cons l Ls ih =>
      intro R hR vs s v ht hv hw hx hb
      have hl : (Check.litRev l).length = (encodeNat l.1).length + 1 := Check.litRev_length l
      simp only [List.flatMap_cons, List.length_append] at hb
      obtain ⟨v₁, r₁⟩ := ih (Check.litRev l ++ R) (by simp [Check.litRev, Sym.bit?]) vs s v
        (by simp [ht]) hv hw hx (by omega)
      set vs' := Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs
      have hvs' := vstk_lits_le Ls vs
      obtain ⟨v₂, r₂⟩ := alit_run l R hR vs' { s with
        t := Check.litRev l ++ R, f := Ls.flatMap litToks ++ s.f, v := vstk vs' } v₁ rfl rfl hw hx
      refine ⟨v₂, runLe_cast (r₁.trans r₂) ?_ ?_⟩
      · simp only [List.flatMap_cons, List.length_append]
        nlinarith
      · simp [vs', List.append_assoc]

theorem clRev_len (C : CNFClause) :
    (Check.clRev C).length = (C.flatMap Check.litRev).length + 1 := by
  simp [Check.clRev, List.length_flatMap, List.map_reverse, List.sum_reverse]

/-- One clause of phase A, from its `cl` token. -/
theorem aclause_run (Lb : ℕ) (C : CNFClause) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl)
    (vs : List ℕ) (s : MS) (v : Bool) (ht : s.t = Check.clRev C ++ R) (hv : s.v = vstk vs)
    (hw : s.w = []) (hx : s.x = []) (hb : (vstk vs).length + (Check.clRev C).length ≤ Lb) :
    ∃ v', RunLe prog ((Check.clRev C).length * (8 * Lb + 12)) ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', { s with
        t := R, f := clauseToks C ++ s.f, v := vstk ((C.map Prod.fst).foldr insV vs),
        c := s.c + 1, mm := s.mm + 3 }.stk⟩ := by
  have hRb : R.head?.bind Sym.bit? = none := by rcases hR with rfl | h <;> simp [Sym.bit?, *]
  have r₁ := a0_cl s v (C.reverse.flatMap Check.litRev ++ R) (by simp [ht, Check.clRev])
  rw [clRev_len] at hb ⊢
  obtain ⟨v₂, r₂⟩ := alits_run Lb C R hRb vs { s with
    t := C.reverse.flatMap Check.litRev ++ R, f := Sym.cl :: s.f, c := s.c + 1,
    mm := s.mm + 3 } true rfl hv hw hx (by omega)
  refine ⟨v₂, runLe_cast ((r₁.le le_rfl).trans r₂) (by nlinarith) ?_⟩
  simp [clauseToks, foldr_lits]

theorem vstk_varsOf_le (φ : CNF) (vs : List ℕ) :
    (vstk ((varsOf φ).foldr insV vs)).length ≤
      (vstk vs).length + (φ.reverse.flatMap Check.clRev).length := by
  induction φ with
  | nil => simp [varsOf]
  | cons C φ ih =>
      have h := vstk_lits_le C ((varsOf φ).foldr insV vs)
      rw [foldr_lits] at h
      have := clRev_len C
      simp only [varsOf_cons, List.foldr_append, List.reverse_cons, List.flatMap_append,
        List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h ih ⊢
      omega

/-- The clauses `φ` of phase A, met last-first above a rest `R`. -/
theorem aformula_run (Lb : ℕ) : ∀ (φ : CNF) (R : List Sym), (R = [] ∨ R.head? = some .cl) →
    ∀ (vs : List ℕ) (s : MS) (v : Bool), s.t = φ.reverse.flatMap Check.clRev ++ R →
    s.v = vstk vs → s.w = [] → s.x = [] →
    (vstk vs).length + (φ.reverse.flatMap Check.clRev).length ≤ Lb →
    ∃ v', RunLe prog ((φ.reverse.flatMap Check.clRev).length * (8 * Lb + 12))
      ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', { s with
        t := R, f := toks φ ++ s.f, v := vstk ((varsOf φ).foldr insV vs),
        c := s.c + φ.length, mm := s.mm + 3 * φ.length }.stk⟩ := by
  intro φ
  induction φ with
  | nil =>
      intro R _ vs s v ht hv _ _ _
      have e : ({ s with
          t := R, f := toks [] ++ s.f, v := vstk ((varsOf []).foldr insV vs),
          c := s.c + List.length ([] : CNF), mm := s.mm + 3 * List.length ([] : CNF) } : MS) =
          s := by
        cases s; simp_all [toks, varsOf]
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by rw [e])⟩
  | cons C φ ih =>
      intro R hR vs s v ht hv hw hx hb
      have hl : ((C :: φ).reverse.flatMap Check.clRev).length =
          (φ.reverse.flatMap Check.clRev).length + (Check.clRev C).length := by simp
      obtain ⟨v₁, r₁⟩ := ih (Check.clRev C ++ R) (Or.inr rfl) vs s v (by simp [ht]) hv hw hx
        (by omega)
      have hvs := vstk_varsOf_le φ vs
      obtain ⟨v₂, r₂⟩ := aclause_run Lb C R hR ((varsOf φ).foldr insV vs) { s with
        t := Check.clRev C ++ R, f := toks φ ++ s.f, v := vstk ((varsOf φ).foldr insV vs),
        c := s.c + φ.length, mm := s.mm + 3 * φ.length } v₁ rfl rfl hw hx (by omega)
      refine ⟨v₂, runLe_cast (r₁.trans r₂) (by rw [hl]; nlinarith) ?_⟩
      simp [toks, varsOf_cons, List.foldr_append, List.append_assoc]
      congr 2

/-- The initial state of the emitter: the token stack, the output stack `o`, the rest empty. -/
def initMS (φ : CNF) (o : List Bool) : MS :=
  ⟨(toks φ).reverse, o, [], [], [], [], [], [], 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The state after phase A and `b0`, `b1`: tokens on `F`, distinct variables on `V`, `C = m`,
`M = 3 m`, `P = m`. -/
def diaMS (φ : CNF) (o : List Bool) : MS :=
  ⟨[], o, toks φ, vstk (hamVars φ), [], [], [], [], φ.length, 3 * φ.length, φ.length, 0, 0, 0,
    0, 0⟩

/-- **Phase A**, then `P := m`. -/
theorem phaseA_run (φ : CNF) (o : List Bool) (v : Bool) :
    ∃ v', RunLe prog ((toks φ).length * (8 * (toks φ).length + 12) + 2 * φ.length + 3)
      ⟨some .a0, v, (initMS φ o).stk⟩ ⟨some .h0, v', (diaMS φ o).stk⟩ := by
  have hT := Check.toks_reverse φ
  have hL : (φ.reverse.flatMap Check.clRev).length = (toks φ).length := by
    rw [← hT, List.length_reverse]
  obtain ⟨v₁, r₁⟩ := aformula_run (toks φ).length φ [] (Or.inl rfl) [] (initMS φ o) v
    (by simp [initMS, hT]) rfl rfl rfl (by simp [vstk, hL])
  rw [hL] at r₁
  set s₁ : MS := { initMS φ o with
    t := [], f := toks φ ++ (initMS φ o).f, v := vstk ((varsOf φ).foldr insV []),
    c := (initMS φ o).c + φ.length, mm := (initMS φ o).mm + 3 * φ.length } with hs₁
  have r₂ := a0_nil s₁ v₁ rfl
  obtain ⟨v₃, r₃⟩ := cp_run (a := .C) (c := .P) Sym.cl Sym.cl (by decide) (by decide) (by decide)
    (l₁ := .b0) (l₂ := .b1) (next := .h0) rfl rfl φ.length true s₁.stk (by simp [s₁, initMS])
    rfl
  have e : update s₁.stk .P (cnt Sym.cl φ.length ++ s₁.stk .P) = (diaMS φ o).stk := by
    have : cnt Sym.cl φ.length ++ s₁.stk .P = cnt Sym.cl φ.length := by simp [s₁, initMS]
    rw [this, upd_P]
    simp [s₁, initMS, diaMS, hamVars_eq]
  rw [e] at r₃
  exact ⟨v₃, runLe_cast (r₁.trans ((r₂.trans r₃).le le_rfl)) (by omega) rfl⟩

end Cslib.Complexity.Karp.EmitHam
