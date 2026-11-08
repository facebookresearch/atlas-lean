/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.SatCheck

/-!
# SAT ≤ 3-COLOR, component 2: the emitter machine

A `TM2` machine that walks the token stack `(toks φ).reverse` of
`Cslib.Complexity.SatVerifier` and pushes the 3-COLOR instance `toCol φ` onto the output stack
`O`, so that `O` reads the instance top-first (`run`).

* `toCol φ` is `next` in unary, then the edges of `colSt φ` in reverse emission order, so the
  machine pushes every edge `(u, v)` in emission order as `false`, `v` ones, `false`, `u` ones
  (`out`), and at the end `false` and `next` ones.
* The token stack lists the clauses last-first and, per clause, the literals last-first: the
  order in which `colSt` walks them. The next free vertex is the unary counter `N`, the current
  OR output the counter `R`. Earlier occurrences lie on `D`, latest on top, each as a marker
  `lit p` above its name bits and its literal vertex `L'` in unary (`dTok`).
* Every edge endpoint is a counter (`N`, `R`, or `U`, which holds an earlier `L'`) plus a
  constant. A copy site (`Site`) pushes a constant block and then a counter's value in ones,
  restoring the counter through the scratch stack `W` (`site_run`); fixed lists of sites
  (`chain_run`) push the occurrence triangle, the consistency edges, the OR gadget, the clause
  end, the empty clause and the vertex count.
* A new occurrence walks `D`, comparing names with `cmpB` (restored with `moveB_restore`); on a
  match it moves the earlier `L'` to `U` and pushes the consistency edges (`consEdges`). The walk
  moves `D` to `E`, which is moved back before the occurrence goes on `D`. `N` is advanced after
  the occurrence's edges: by `2` for a clause's first literal (flag `F`), by `5` after an OR
  gadget, with `R` set to the new output.

The proof follows the CLIQUE emitter: one-step lemmas on the quiescent states `MS.stk`, the walk
over `D` by induction (`walk_run`), then literals, clauses and the formula by forward induction,
with the size invariant `Sz` bounding the counters and `D`. The step count is cubic in
`|toks φ|`; `run` states it as `500 (|toks φ| + 1)⁴`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitColor

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability Cslib.Complexity.SatVerifier

/-! ### The output, edge by edge -/

/-- The bits of an edge `(u, v)` in `encodeE`: `u` ones, `false`, `v` ones, `false`. -/
def eB (e : ℕ × ℕ) : List Bool :=
  List.replicate e.1 true ++ false :: (List.replicate e.2 true ++ [false])

/-- The output pushed for the edges `em`, emitted in order (the last one on top). -/
def out (em : List (ℕ × ℕ)) : List Bool := em.reverse.flatMap eB

theorem out_append (xs ys : List (ℕ × ℕ)) : out (xs ++ ys) = out ys ++ out xs := by
  simp [out]

theorem toCol_eq (φ : CNF) :
    toCol φ = List.replicate (colSt φ).next true ++ false :: out (colSt φ).em := rfl

/-! ### The machine -/

/-- Stacks: tokens, output, the next free vertex, the current OR output, earlier occurrences,
the walk's other side, the current name, its polarity, the first-literal flag, an earlier
literal vertex, and scratch stacks (`X`, `B` for comparisons, `W` for copies). -/
inductive K | T | O | N | R | D | E | A | P | F | U | X | B | W
  deriving DecidableEq

/-- The stacks, enumerated. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, K.O, K.N, K.R, K.D, K.E, K.A, K.P, K.F, K.U, K.X, K.B, K.W], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Stack alphabets: the output stack holds bits, the others token symbols (counters hold
`Sym.cl`). -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- The counters a copy site reads: the next vertex, the OR output, an earlier literal
vertex. -/
inductive Src | n | r | u
  deriving DecidableEq

/-- The stack of a counter. -/
def Src.k : Src → K
  | .n => .N
  | .r => .R
  | .u => .U

/-- The unit symbol of a counter. -/
def Src.unit : (s : Src) → Γ s.k
  | .n => Sym.cl
  | .r => Sym.cl
  | .u => Sym.cl

/-- Copy sites: the occurrence triangle (`o`), the consistency edges for equal (`c`) and
opposite (`d`) polarity, the OR gadget (`r`), the clause end (`e`), the empty clause (`z`) and
the vertex count (`fin`). -/
inductive Site
  | o1 | o2 | o3 | o4 | c1 | c2 | c3 | c4 | d1 | d2 | d3 | d4
  | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | e1 | e2 | z1 | z2 | z3 | fin
  deriving DecidableEq

/-- The sites, listed. -/
def Site.all : List Site :=
  [.o1, .o2, .o3, .o4, .c1, .c2, .c3, .c4, .d1, .d2, .d3, .d4, .r1, .r2, .r3, .r4, .r5, .r6, .r7,
    .r8, .r9, .r10, .r11, .e1, .e2, .z1, .z2, .z3, .fin]

/-- The sites, enumerated. -/
instance Site.instFintypeEnumFix : Fintype Site :=
  Fintype.ofList Site.all (fun x => by cases x <;> decide)

/-- The counter a site copies. -/
def Site.src : Site → Src
  | .c2 | .c4 | .d2 | .d4 => .u
  | .r4 | .e1 | .e2 => .r
  | _ => .n

/-- The constant block a site pushes below its counter copy, read top-first. -/
def Site.top : Site → List Bool
  | .o1 => [true, false]
  | .o2 => [false]
  | .o3 => [false, true, true, false]
  | .o4 => [true, false, true, true, false]
  | .c1 => [true, false]
  | .c2 => [false]
  | .c3 => [false]
  | .c4 => [true, false]
  | .d1 => [false]
  | .d2 => [false]
  | .d3 => [true, false]
  | .d4 => [true, false]
  | .r1 => [true, true, false]
  | .r2 => [false]
  | .r3 => [true, true, true, false]
  | .r4 => [false]
  | .r5 => [true, true, true, false]
  | .r6 => [true, true, false]
  | .r7 => [true, true, true, true, false]
  | .r8 => [true, true, false]
  | .r9 => [true, true, true, true, false]
  | .r10 => [true, true, true, false]
  | .r11 => [true, true, true, true, false, true, true, false]
  | .e1 => [false, true, false]
  | .e2 => [false, true, true, false]
  | .z1 => [false, false]
  | .z2 => [false, true, false]
  | .z3 => [false, true, true, false]
  | .fin => [false]

/-- Labels. `init`: palette; `cls`: next clause; `lits`: next literal; `lp`, `nm`: pop the
polarity and the name; `walk` to `dr`: walk `D` (compare, restore, select the polarity case,
move the name and the vertex to `E`, or the vertex to `U` and push the consistency edges);
`back`: move `E` back to `D`; `putN` to `putP`: put the occurrence on `D`; `aft`, `fA` to `fC`:
set `R` and advance `N`; `clr`: clear `R`; `zN`: advance `N` after an empty clause; `pre j`,
`cpA j`, `cpB j`: copy site `j`. -/
inductive Lab
  | init | cls | lits | lp | nm | walk | cmp | rsA (e : Bool) | rsD (e : Bool) | sel
  | mvN (r : Option Bool) | skU | mvU (b : Bool) | dr | back | putN | putW | putA | putB | putP
  | aft | fA (b : Bool) | fB (b : Bool) | fC (b : Bool) | clr (b : Bool) | zN
  | pre (j : Site) | cpA (j : Site) | cpB (j : Site) | done
  deriving DecidableEq

/-- The labels, enumerated. -/
instance Lab.instFintypeEnumFix : Fintype Lab :=
  Fintype.ofList
    ([Lab.init, .cls, .lits, .lp, .nm, .walk, .cmp, .sel, .mvN none, .skU, .dr, .back, .putN,
        .putW, .putA, .putB, .putP, .aft, .zN, .done] ++
      ([true, false].flatMap fun b =>
        [Lab.rsA b, .rsD b, .mvN (some b), .mvU b, .fA b, .fB b, .fC b, .clr b]) ++
      (Site.all.flatMap fun j => [Lab.pre j, .cpA j, .cpB j]))
    (fun x => by
      cases x <;> (try rename_i a; cases a) <;> (try rename_i a; cases a) <;> decide)

/-- Where a site continues. -/
def Site.nxt : Site → Lab
  | .o1 => .pre .o2
  | .o2 => .pre .o3
  | .o3 => .pre .o4
  | .o4 => .lp
  | .c1 => .pre .c2
  | .c2 => .pre .c3
  | .c3 => .pre .c4
  | .c4 => .dr
  | .d1 => .pre .d2
  | .d2 => .pre .d3
  | .d3 => .pre .d4
  | .d4 => .dr
  | .r1 => .pre .r2
  | .r2 => .pre .r3
  | .r3 => .pre .r4
  | .r4 => .pre .r5
  | .r5 => .pre .r6
  | .r6 => .pre .r7
  | .r7 => .pre .r8
  | .r8 => .pre .r9
  | .r9 => .pre .r10
  | .r10 => .pre .r11
  | .r11 => .clr true
  | .e1 => .pre .e2
  | .e2 => .clr false
  | .z1 => .pre .z2
  | .z2 => .pre .z3
  | .z3 => .zN
  | .fin => .done

/-- Is the top of a stack a literal marker? -/
def isLit : Option Sym → Bool
  | some (.lit _) => true
  | _ => false

/-- Read a symbol as a unary unit (`cl`); every other symbol ends a run of units. -/
def unitOf : Sym → Option Bool
  | .cl => some true
  | _ => none

/-- The palette triangle, as pushed. -/
def pal : List Bool := out [(0, 1), (0, 2), (1, 2)]

/-- The machine. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .init => pushList .O pal.reverse <| pushList .N [Sym.cl, Sym.cl, Sym.cl] <|
      .goto fun _ => .cls
  | .cls => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .pre .fin) <|
      .pop .T (fun s _ => s) <| .peek .T (fun _ o => isLit o) <| .branch id
        (.push .F (fun _ => Sym.cl) <| .goto fun _ => .lits) (.goto fun _ => .pre .z1)
  | .lits => .peek .T (fun _ o => isLit o) <| .branch id (.goto fun _ => .pre .o1)
      (.goto fun _ => .pre .e1)
  | .lp => .pop .T (fun _ o => o == some (.lit true)) <| .push .P (fun s => Sym.lit s) <|
      .goto fun _ => .nm
  | .nm => moveB .T .A Sym.bit? Sym.bit .nm .walk
  | .walk => .peek .D (fun _ o => o.isNone) <| .branch id (.goto fun _ => .back) <|
      .pop .D (fun _ o => o == some (.lit true)) <| .push .E (fun s => Sym.lit s) <|
        .goto fun _ => .cmp
  | .cmp => cmpB .A .D .X .B Sym.bit? Sym.bit? Sym.bit Sym.bit .cmp (.rsA true) (.rsA false)
  | .rsA e => moveB .X .A Sym.bit? Sym.bit (.rsA e) (.rsD e)
  | .rsD e => moveB .B .D Sym.bit? Sym.bit (.rsD e) (if e then .sel else .mvN none)
  | .sel => .peek .E (fun _ o => o == some (.lit true)) <|
      .peek .P (fun s o => s == (o == some (.lit true))) <| .goto fun s => .mvN (some s)
  | .mvN r => moveB .D .E Sym.bit? Sym.bit (.mvN r) (r.elim .skU .mvU)
  | .skU => moveB .D .E unitOf (fun _ => Sym.cl) .skU .walk
  | .mvU b => moveB .D .U unitOf (fun _ => Sym.cl) (.mvU b) (.pre (if b then .c1 else .d1))
  | .dr => xfer .U [⟨.E, Sym.cl⟩] .dr .walk
  | .back => .peek .E (fun _ o => o.isNone) <| .branch id (.goto fun _ => .putN) <|
      .peek .E (fun _ o => o == some .cl) <| .branch id
        (.pop .E (fun s _ => s) <| .push .D (fun _ => Sym.cl) <| .goto fun _ => .back) <|
      .peek .E (fun _ o => isLit o) <| .branch id
        (.pop .E (fun _ o => o == some (.lit true)) <| .push .D (fun s => Sym.lit s) <|
          .goto fun _ => .back)
        (.pop .E (fun _ o => o == some (.bit true)) <| .push .D (fun s => Sym.bit s) <|
          .goto fun _ => .back)
  | .putN => xfer .N [⟨.D, Sym.cl⟩, ⟨.W, Sym.cl⟩] .putN .putW
  | .putW => xfer .W [⟨.N, Sym.cl⟩] .putW .putA
  | .putA => moveB .A .B Sym.bit? Sym.bit .putA .putB
  | .putB => moveB .B .D Sym.bit? Sym.bit .putB .putP
  | .putP => .pop .P (fun _ o => o == some (.lit true)) <| .push .D (fun s => Sym.lit s) <|
      .goto fun _ => .aft
  | .aft => decr .F (.pre .r1) (.fA true)
  | .fA b => xfer .N [⟨.R, Sym.cl⟩, ⟨.W, Sym.cl⟩] (.fA b) (.fB b)
  | .fB b => xfer .W [⟨.N, Sym.cl⟩] (.fB b) (.fC b)
  | .fC b => pushList .R (cnt Sym.cl (if b then 0 else 4)) <|
      emit .N (cnt Sym.cl (if b then 2 else 5)) .lits
  | .clr b => xfer .R [] (.clr b) (if b then .fA false else .cls)
  | .zN => emit .N [Sym.cl] .cls
  | .pre j => emitR .O j.top (.cpA j)
  | .cpA j => xfer j.src.k [⟨.O, true⟩, ⟨.W, Sym.cl⟩] (.cpA j) (.cpB j)
  | .cpB j => xfer .W [⟨j.src.k, j.src.unit⟩] (.cpB j) j.nxt
  | .done => .halt

/-- The start label. -/
def start : Lab := .init

/-! ### Quiescent states -/

/-- A quiescent state: `N`, `R`, `F`, `U` are unary counters of `Sym.cl` and the scratch stacks
`X`, `B`, `W` are empty. -/
structure MS where
  /-- The token stack. -/
  t : List Sym
  /-- The output stack. -/
  o : List Bool
  /-- The next free vertex. -/
  n : ℕ
  /-- The current OR output. -/
  r : ℕ
  /-- Earlier occurrences. -/
  d : List Sym
  /-- The walk's other side. -/
  e : List Sym
  /-- The current name. -/
  a : List Sym
  /-- The current polarity. -/
  p : List Sym
  /-- The first-literal flag. -/
  f : ℕ
  /-- An earlier literal vertex. -/
  u : ℕ

/-- The stacks of a quiescent state. -/
def MS.stk (m : MS) : ∀ k, List (Γ k)
  | .T => m.t
  | .O => m.o
  | .N => cnt Sym.cl m.n
  | .R => cnt Sym.cl m.r
  | .D => m.d
  | .E => m.e
  | .A => m.a
  | .P => m.p
  | .F => cnt Sym.cl m.f
  | .U => cnt Sym.cl m.u
  | .X | .B | .W => []

/-- The value of a counter. -/
def MS.val (m : MS) : Src → ℕ
  | .n => m.n
  | .r => m.r
  | .u => m.u

section MSLemmas

variable (m : MS)

@[simp] theorem stk_T : m.stk .T = m.t := rfl
@[simp] theorem stk_O : m.stk .O = m.o := rfl
@[simp] theorem stk_N : m.stk .N = List.replicate m.n Sym.cl := rfl
@[simp] theorem stk_R : m.stk .R = List.replicate m.r Sym.cl := rfl
@[simp] theorem stk_D : m.stk .D = m.d := rfl
@[simp] theorem stk_E : m.stk .E = m.e := rfl
@[simp] theorem stk_A : m.stk .A = m.a := rfl
@[simp] theorem stk_P : m.stk .P = m.p := rfl
@[simp] theorem stk_F : m.stk .F = List.replicate m.f Sym.cl := rfl
@[simp] theorem stk_U : m.stk .U = List.replicate m.u Sym.cl := rfl
@[simp] theorem stk_X : m.stk .X = [] := rfl
@[simp] theorem stk_B : m.stk .B = [] := rfl
@[simp] theorem stk_W : m.stk .W = [] := rfl

@[simp] theorem upd_T (x : List Sym) : update m.stk .T x = {m with t := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_O (x : List Bool) : update m.stk .O x = {m with o := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_D (x : List Sym) : update m.stk .D x = {m with d := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_E (x : List Sym) : update m.stk .E x = {m with e := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_A (x : List Sym) : update m.stk .A x = {m with a := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_P (x : List Sym) : update m.stk .P x = {m with p := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_R (j : ℕ) :
    update m.stk .R (List.replicate j Sym.cl) = {m with r := j}.stk := by
  funext k; cases k <;> rfl
theorem upd_F_nil : update m.stk .F [] = {m with f := 0}.stk := by
  funext k; cases k <;> rfl

theorem stk_src (s : Src) : m.stk s.k = cnt s.unit (m.val s) := by cases s <;> rfl

theorem val_le (s : Src) : m.val s ≤ m.n + m.r + m.u := by
  cases s <;> simp only [MS.val] <;> omega

end MSLemmas

@[simp] private theorem sym_beq (a b : Sym) : (a == b) = decide (a = b) := rfl

theorem run_cast {k k' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : Run prog k c d)
    (hk : k = k') (hd : d = d') : Run prog k' c d' := hk ▸ hd ▸ h

theorem runLe_cast {k k' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog k c d)
    (hk : k ≤ k') (hd : d = d') : RunLe prog k' c d' := hd ▸ h.mono hk

/-! ### Copy sites -/

theorem Src.k_ne_O (s : Src) : s.k ≠ .O := by cases s <;> decide

theorem Src.k_ne_W (s : Src) : s.k ≠ .W := by cases s <;> decide

/-- Copy counter `s` onto stack `c`, one `x` per unit, restoring it through `W`: `2 v + 2` steps
for the value `v`. -/
theorem dup_run (s : Src) {c : K} (x : Γ c) (hc : c ≠ s.k) (hcW : c ≠ .W) {l₁ l₂ next : Lab}
    (h₁ : prog l₁ = xfer s.k [⟨c, x⟩, ⟨.W, Sym.cl⟩] l₁ l₂)
    (h₂ : prog l₂ = xfer .W [⟨s.k, s.unit⟩] l₂ next) (val : ℕ) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : S s.k = cnt s.unit val) (hW : S .W = []) :
    ∃ v', Run prog (2 * val + 2) ⟨some l₁, v, S⟩
      ⟨some next, v', update S c (cnt x val ++ S c)⟩ := by
  have hsW := s.k_ne_W
  have r₁ := xfer_run h₁ (pair_nodupKeys x (Sym.cl : Γ .W) hcW) (by simp [hc.symm, hsW]) s.unit
    val v S hS
  set S₁ := addU [⟨c, x⟩, ⟨.W, Sym.cl⟩] val (update S s.k []) with hS₁
  have h₁W : S₁ .W = cnt (Sym.cl : Γ .W) val := by
    rw [hS₁, addU_pair_snd _ _ _ _ hcW.symm, update_of_ne hsW.symm, hW, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys s.unit) (by simp [hsW.symm]) (Sym.cl : Γ .W) val
    (Flag.tag false) S₁ h₁W
  have hfin : addU [⟨s.k, s.unit⟩] val (update S₁ .W []) = update S c (cnt x val ++ S c) := by
    funext k
    by_cases hks : k = s.k
    · subst hks
      rw [addU_single_self, update_of_ne hsW, hS₁, addU_pair_ne _ _ _ _ hc.symm hsW,
        update_self, update_of_ne hc.symm, hS, List.append_nil]
    rw [addU_single_ne _ _ _ hks]
    by_cases hkW : k = .W
    · subst hkW; rw [update_self, update_of_ne hcW.symm, hW]
    rw [update_of_ne hkW]
    by_cases hkc : k = c
    · subst hkc; rw [hS₁, addU_pair_fst, update_of_ne hc, update_self]
    rw [hS₁, addU_pair_ne _ _ _ _ hkc hkW, update_of_ne hks, update_of_ne hkc]
  rw [hfin] at r₂
  exact ⟨_, (r₁.trans r₂).of_eq (by omega)⟩

/-- The bits site `j` pushes from state `m`: its counter in ones above its constant block. -/
def atom (m : MS) (j : Site) : List Bool := List.replicate (m.val j.src) true ++ j.top

/-- A copy site: from `pre j`, push `atom m j` and continue at `j.nxt`. -/
theorem site_run (j : Site) (m : MS) (v : Bool) :
    ∃ v', Run prog (2 * m.val j.src + 3) ⟨some (.pre j), v, m.stk⟩
      ⟨some j.nxt, v', {m with o := atom m j ++ m.o}.stk⟩ := by
  have r₁ := emitR_run (M := prog) (self := .pre j) (next := .cpA j) (k := .O) (ys := j.top) rfl
    v m.stk
  obtain ⟨v', r₂⟩ := dup_run j.src (true : Γ .O) (Ne.symm j.src.k_ne_O) (by decide)
    (l₁ := .cpA j) (l₂ := .cpB j) (next := j.nxt) rfl rfl (m.val j.src) v
    (update m.stk .O (j.top ++ m.stk .O))
    (by rw [update_of_ne j.src.k_ne_O]; exact stk_src m j.src) rfl
  have e : update (update m.stk .O (j.top ++ m.stk .O)) .O
      (cnt true (m.val j.src) ++ update m.stk .O (j.top ++ m.stk .O) .O) =
      {m with o := atom m j ++ m.o}.stk := by simp [atom]
  rw [e] at r₂
  exact ⟨v', (r₁.trans r₂).of_eq (by omega)⟩

/-- The sites `js` run in sequence from label `l₀`, the last one continuing at `l`. -/
def Chain : List Site → Lab → Lab → Bool
  | [], l₀, l => l₀ == l
  | j :: js, l₀, l => l₀ == .pre j && Chain js j.nxt l

/-- The bits a run of sites pushes, the last site's on top. -/
def chainOut (m : MS) (js : List Site) : List Bool := (js.map (atom m)).reverse.flatten

@[simp] theorem chainOut_nil (m : MS) : chainOut m [] = [] := rfl

@[simp] theorem chainOut_cons (m : MS) (j : Site) (js : List Site) :
    chainOut m (j :: js) = chainOut m js ++ atom m j := by simp [chainOut]

theorem chainOut_o (m : MS) (x : List Bool) (js : List Site) :
    chainOut {m with o := x} js = chainOut m js := rfl

/-- A run of sites pushes `chainOut m js`, `2 (n + r + u) + 3` steps per site. -/
theorem chain_run (js : List Site) : ∀ (m : MS) (l₀ l : Lab), Chain js l₀ l = true →
    ∀ v : Bool, ∃ v', RunLe prog (js.length * (2 * (m.n + m.r + m.u) + 3)) ⟨some l₀, v, m.stk⟩
      ⟨some l, v', {m with o := chainOut m js ++ m.o}.stk⟩ := by
  induction js with
  | nil =>
      intro m l₀ l h v
      simp only [Chain, beq_iff_eq] at h
      subst h
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) rfl⟩
  | cons j js ih =>
      intro m l₀ l h v
      simp only [Chain, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨v₁, r₁⟩ := site_run j m v
      obtain ⟨v₂, r₂⟩ := ih {m with o := atom m j ++ m.o} j.nxt l h v₁
      refine ⟨v₂, runLe_cast ((r₁.le le_rfl).trans r₂) ?_ ?_⟩
      · have := val_le m j.src
        simp only [List.length_cons, add_mul, one_mul]
        omega
      · simp [chainOut_o, List.append_assoc]

/-! ### One-step lemmas -/

/-- Symbols the walk moves between `D` and `E`. -/
def isTok : Sym → Bool
  | .bit _ | .lit _ | .cl => true
  | _ => false

section Steps

variable (m : MS) (v : Bool)

theorem init_step : Run prog 1 ⟨some .init, v, m.stk⟩
    ⟨some .cls, v, {m with o := pal ++ m.o, n := m.n + 3}.stk⟩ := by
  refine Run.single ?_
  simp only [prog, stepAux_pushList, TM2.stepAux]
  congr 1
  funext k; cases k <;> simp [List.replicate_succ]

theorem cls_nil (h : m.t = []) :
    Run prog 1 ⟨some .cls, v, m.stk⟩ ⟨some (.pre .fin), true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem cls_lit (R : List Sym) (h : m.t = .cl :: R) (hR : isLit R.head? = true) :
    Run prog 1 ⟨some .cls, v, m.stk⟩ ⟨some .lits, true, {m with t := R, f := m.f + 1}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_T, h, List.head?_cons, Option.isNone_some, id,
      Bool.cond_false, List.tail_cons, upd_T, hR, Bool.cond_true]
    congr 1; funext k; cases k <;> simp [List.replicate_succ])

theorem cls_emp (R : List Sym) (h : m.t = .cl :: R) (hR : isLit R.head? = false) :
    Run prog 1 ⟨some .cls, v, m.stk⟩ ⟨some (.pre .z1), false, {m with t := R}.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h, hR])

theorem lits_lit (h : isLit m.t.head? = true) :
    Run prog 1 ⟨some .lits, v, m.stk⟩ ⟨some (.pre .o1), true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem lits_end (h : isLit m.t.head? = false) :
    Run prog 1 ⟨some .lits, v, m.stk⟩ ⟨some (.pre .e1), false, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem lp_step (b : Bool) (R : List Sym) (h : m.t = .lit b :: R) :
    Run prog 1 ⟨some .lp, v, m.stk⟩ ⟨some .nm, b, {m with t := R, p := .lit b :: m.p}.stk⟩ :=
  Run.single (by cases b <;> simp [prog, TM2.stepAux, h])

theorem walk_nil (h : m.d = []) :
    Run prog 1 ⟨some .walk, v, m.stk⟩ ⟨some .back, true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem walk_lit (b : Bool) (R : List Sym) (h : m.d = .lit b :: R) :
    Run prog 1 ⟨some .walk, v, m.stk⟩ ⟨some .cmp, b, {m with d := R, e := .lit b :: m.e}.stk⟩ :=
  Run.single (by cases b <;> simp [prog, TM2.stepAux, h])

theorem sel_step (q b : Bool) (R : List Sym) (hE : m.e = .lit q :: R) (hP : m.p = [.lit b]) :
    Run prog 1 ⟨some .sel, v, m.stk⟩ ⟨some (.mvN (some (q == b))), q == b, m.stk⟩ :=
  Run.single (by cases q <;> cases b <;> simp [prog, TM2.stepAux, hE, hP])

theorem putP_step (b : Bool) (h : m.p = [.lit b]) :
    Run prog 1 ⟨some .putP, v, m.stk⟩ ⟨some .aft, b, {m with p := [], d := .lit b :: m.d}.stk⟩ :=
  Run.single (by cases b <;> simp [prog, TM2.stepAux, h])

theorem back_nil (h : m.e = []) :
    Run prog 1 ⟨some .back, v, m.stk⟩ ⟨some .putN, true, m.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem back_step (s : Sym) (hs : isTok s = true) (R : List Sym) (h : m.e = s :: R) :
    ∃ v', Run prog 1 ⟨some .back, v, m.stk⟩
      ⟨some .back, v', {m with e := R, d := s :: m.d}.stk⟩ := by
  cases s with
  | bit b => exact ⟨b, Run.single (by cases b <;> simp [prog, TM2.stepAux, isLit, h])⟩
  | lit q => exact ⟨q, Run.single (by cases q <;> simp [prog, TM2.stepAux, isLit, h])⟩
  | cl => exact ⟨true, Run.single (by simp [prog, TM2.stepAux, h])⟩
  | val _ => simp [isTok] at hs
  | dead => simp [isTok] at hs

theorem aft_pos (h : m.f = 1) :
    ∃ v', Run prog 1 ⟨some .aft, v, m.stk⟩ ⟨some (.fA true), v', {m with f := 0}.stk⟩ := by
  have := decr_run_pos (M := prog) (self := .aft) rfl v (S := m.stk) (x := Sym.cl) (r := [])
    (by simp [h])
  rw [upd_F_nil] at this
  exact ⟨_, this⟩

theorem aft_zero (h : m.f = 0) :
    ∃ v', Run prog 1 ⟨some .aft, v, m.stk⟩ ⟨some (.pre .r1), v', m.stk⟩ :=
  ⟨_, decr_run_zero (M := prog) (self := .aft) rfl v (by simp [h])⟩

theorem fC_step (b : Bool) : Run prog 1 ⟨some (.fC b), v, m.stk⟩ ⟨some .lits, v,
    {m with r := m.r + (if b then 0 else 4), n := m.n + (if b then 2 else 5)}.stk⟩ := by
  refine Run.single ?_
  simp only [prog, emit, stepAux_pushList, TM2.stepAux]
  congr 1
  funext k; cases k <;> cases b <;> simp [List.replicate_succ]

theorem zN_step : Run prog 1 ⟨some .zN, v, m.stk⟩ ⟨some .cls, v, {m with n := m.n + 1}.stk⟩ := by
  refine Run.single ?_
  simp only [prog, emit, stepAux_pushList, TM2.stepAux]
  congr 1; funext k; cases k <;> simp [List.replicate_succ]

end Steps

/-! ### Phases -/

/-- The name bits of variable `x`, as the stacks `A` and `D` hold them. -/
abbrev name (x : ℕ) : List Sym := (encodeNat x).map Sym.bit

/-- An occurrence on `D`: its polarity marker above its name bits and its literal vertex in
unary. -/
def dTok (q : ℕ × Bool × ℕ × ℕ) : List Sym := .lit q.2.1 :: (name q.1 ++ cnt Sym.cl q.2.2.1)

section Phases

variable (m : MS) (v : Bool)

private theorem isBitBlock_map (u : List Bool) : IsBitBlock Sym.bit? (u.map Sym.bit) u := by
  simp [IsBitBlock, Function.comp_def, Sym.bit?]

private theorem isBitBlock_map_reverse (u : List Bool) :
    IsBitBlock Sym.bit? (u.map Sym.bit).reverse u.reverse := by
  simp [IsBitBlock, Function.comp_def, Sym.bit?, List.map_reverse]

theorem isBitBlock_cnt (j : ℕ) : IsBitBlock unitOf (cnt Sym.cl j) (List.replicate j true) := by
  simp [IsBitBlock, unitOf]

theorem bit_inv (x : Sym) (b : Bool) (h : Sym.bit? x = some b) : Sym.bit b = x := by
  cases x <;> simp_all [Sym.bit?]

/-- Move the current name from `T` to `A`. -/
theorem nm_run (x : ℕ) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (h : m.t = (name x).reverse ++ R) (hA : m.a = []) :
    ∃ v', Run prog ((encodeNat x).length + 1) ⟨some .nm, v, m.stk⟩
      ⟨some .walk, v', {m with t := R, a := name x}.stk⟩ := by
  obtain ⟨v', S', r, hT, hA', hk⟩ := moveB_run (M := prog) (self := .nm) (next := .walk)
    (a := .T) (b := .A) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) (encodeNat x).reverse
    (name x).reverse R v m.stk (by simp [h]) (isBitBlock_map_reverse _) hR
  have hS : S' = {m with t := R, a := name x}.stk := by
    funext k; cases k <;> simp [hT, hA', hA, hk, List.map_reverse]
  rw [hS, List.length_reverse] at r
  exact ⟨v', r⟩

/-- Compare the current name `u` on `A` with an earlier name `w` on `D` and restore both. -/
theorem cmp_run (u w : List Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (hA : m.a = u.map Sym.bit) (hD : m.d = w.map Sym.bit ++ R) :
    ∃ v', RunLe prog (3 * w.length + 3) ⟨some .cmp, v, m.stk⟩
      ⟨some (if u = w then .sel else .mvN none), v', m.stk⟩ := by
  have hd : Distinct4 K.A K.D K.X K.B :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨cp, v₁, S₁, hcu, hcw, -, r₁, h1A, h1D, h1X, h1B, h1k⟩ := cmpB_run (M := prog)
    (self := .cmp) (eqL := .rsA true) (neL := .rsA false) (a := .A) (b := .D)
    (ta := .X) (tb := .B) (da := Sym.bit?) (db := Sym.bit?) (ea := Sym.bit) (eb := Sym.bit) rfl
    hd u w (u.map Sym.bit) [] (w.map Sym.bit) R v m.stk (by simp [hA]) hD (isBitBlock_map u)
    (isBitBlock_map w) rfl hR
  have hl : (if u = w then Lab.rsA true else Lab.rsA false) = Lab.rsA (decide (u = w)) := by
    split <;> simp_all
  rw [hl] at r₁
  obtain ⟨v₂, S₂, r₂, h2X, h2A, h2k⟩ := moveB_restore (M := prog)
    (self' := .rsA (decide (u = w))) (next := .rsD (decide (u = w))) (t := .X) (a := .A)
    (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit) (da := Sym.bit?) rfl (by decide)
    (fun _ => rfl) bit_inv u cp (u.map Sym.bit) [] [] v₁ S₁ (isBitBlock_map u) hcu
    (by simpa using h1X) h1A rfl
  obtain ⟨v₃, S₃, r₃, h3B, h3D, h3k⟩ := moveB_restore (M := prog)
    (self' := .rsD (decide (u = w))) (next := if decide (u = w) then .sel else .mvN none)
    (t := .B) (a := .D) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit) (da := Sym.bit?) rfl
    (by decide) (fun _ => rfl) bit_inv w cp (w.map Sym.bit) R [] v₂ S₂ (isBitBlock_map w) hcw
    (by simp [h2k, h1B]) (by simp [h2k, h1D]) rfl
  have hS : S₃ = m.stk := by
    funext k; cases k <;> simp [h3B, h3D, h3k, h2X, h2A, h2k, h1k, hA, hD]
  rw [hS] at r₃
  refine ⟨v₃, runLe_cast (((r₁.trans r₂).trans r₃).le le_rfl) ?_ (by simp)⟩
  have := hcw.length_le
  omega

/-- Move an earlier name from `D` to `E`. -/
theorem mvN_run (r : Option Bool) (w : List Bool) (R : List Sym)
    (hR : R.head?.bind Sym.bit? = none) (h : m.d = w.map Sym.bit ++ R) :
    ∃ v', Run prog (w.length + 1) ⟨some (.mvN r), v, m.stk⟩
      ⟨some (r.elim .skU .mvU), v', {m with d := R, e := (w.map Sym.bit).reverse ++ m.e}.stk⟩ := by
  obtain ⟨v', S', r', hD, hE, hk⟩ := moveB_run (M := prog) (self := .mvN r)
    (next := r.elim .skU .mvU) (a := .D) (b := .E) (d := Sym.bit?) (g := Sym.bit) rfl
    (by decide) w (w.map Sym.bit) R v m.stk h (isBitBlock_map _) hR
  have hS : S' = {m with d := R, e := (w.map Sym.bit).reverse ++ m.e}.stk := by
    funext k; cases k <;> simp [hD, hE, hk]
  rw [hS] at r'
  exact ⟨v', r'⟩

/-- Move an earlier literal vertex from `D` to `E`. -/
theorem skU_run (j : ℕ) (R : List Sym) (hR : R.head?.bind unitOf = none)
    (h : m.d = cnt Sym.cl j ++ R) :
    ∃ v', Run prog (j + 1) ⟨some .skU, v, m.stk⟩
      ⟨some .walk, v', {m with d := R, e := cnt Sym.cl j ++ m.e}.stk⟩ := by
  obtain ⟨v', S', r', hD, hE, hk⟩ := moveB_run (M := prog) (self := .skU) (next := .walk)
    (a := .D) (b := .E) (d := unitOf) (g := fun _ => Sym.cl) rfl (by decide)
    (List.replicate j true) (cnt Sym.cl j) R v m.stk h (isBitBlock_cnt j) hR
  have hS : S' = {m with d := R, e := cnt Sym.cl j ++ m.e}.stk := by
    funext k; cases k <;> simp [hD, hE, hk]
  rw [hS, List.length_replicate] at r'
  exact ⟨v', r'⟩

/-- Move an earlier literal vertex from `D` to `U`. -/
theorem mvU_run (b : Bool) (j : ℕ) (R : List Sym) (hR : R.head?.bind unitOf = none)
    (h : m.d = cnt Sym.cl j ++ R) (hU : m.u = 0) :
    ∃ v', Run prog (j + 1) ⟨some (.mvU b), v, m.stk⟩
      ⟨some (.pre (if b then .c1 else .d1)), v', {m with d := R, u := j}.stk⟩ := by
  obtain ⟨v', S', r', hD, hU', hk⟩ := moveB_run (M := prog) (self := .mvU b)
    (next := .pre (if b then .c1 else .d1)) (a := .D) (b := .U) (d := unitOf)
    (g := fun _ => Sym.cl) rfl (by decide) (List.replicate j true) (cnt Sym.cl j) R v m.stk h
    (isBitBlock_cnt j) hR
  have hS : S' = {m with d := R, u := j}.stk := by
    funext k; cases k <;> simp [hD, hU', hk, hU]
  rw [hS, List.length_replicate] at r'
  exact ⟨v', r'⟩

/-- Move `U` onto `E`. -/
theorem dr_run : ∃ v', Run prog (m.u + 1) ⟨some .dr, v, m.stk⟩
    ⟨some .walk, v', {m with u := 0, e := cnt Sym.cl m.u ++ m.e}.stk⟩ := by
  have h := xfer_run (M := prog) (self := .dr) (next := .walk) (k := .U)
    (ps := [⟨.E, Sym.cl⟩]) rfl (single_nodupKeys _) (by simp) Sym.cl m.u v m.stk rfl
  have e : addU [⟨K.E, Sym.cl⟩] m.u (update m.stk .U []) =
      {m with u := 0, e := cnt Sym.cl m.u ++ m.e}.stk := by
    funext k
    by_cases hk : k = .E
    · subst hk; rw [addU_single_self]; rfl
    · rw [addU_single_ne _ _ _ hk]; cases k <;> first | rfl | exact absurd rfl hk
  rw [e] at h
  exact ⟨_, h⟩

/-- Clear `R`. -/
theorem clr_run (b : Bool) : ∃ v', Run prog (m.r + 1) ⟨some (.clr b), v, m.stk⟩
    ⟨some (if b then .fA false else .cls), v', {m with r := 0}.stk⟩ := by
  have h := xfer_run (M := prog) (self := .clr b) (next := if b then .fA false else .cls)
    (k := .R) (ps := []) rfl List.nodupKeys_nil (by simp) Sym.cl m.r v m.stk rfl
  have e : addU [] m.r (update m.stk .R []) = {m with r := 0}.stk := by
    funext k; cases k <;> rfl
  rw [e] at h
  exact ⟨_, h⟩

/-- Add `N` to `R`, restoring `N` through `W`. -/
theorem fAB_run (b : Bool) : ∃ v', Run prog (2 * m.n + 2) ⟨some (.fA b), v, m.stk⟩
    ⟨some (.fC b), v', {m with r := m.n + m.r}.stk⟩ := by
  obtain ⟨v', h⟩ := dup_run .n (c := .R) Sym.cl (by decide) (by decide) (l₁ := .fA b)
    (l₂ := .fB b) (next := .fC b) rfl rfl m.n v m.stk rfl rfl
  have e : update m.stk .R (cnt (Sym.cl : Γ .R) m.n ++ m.stk .R) =
      {m with r := m.n + m.r}.stk := by
    rw [stk_R, ← List.replicate_add]; exact upd_R m _
  rw [e] at h
  exact ⟨v', h⟩

/-- Move `E` back onto `D`, symbol by symbol. -/
theorem back_run : ∀ (L : List Sym), (∀ s ∈ L, isTok s = true) → ∀ (m : MS) (v : Bool),
    m.e = L → ∃ v', Run prog (L.length + 1) ⟨some .back, v, m.stk⟩
      ⟨some .putN, v', {m with e := [], d := L.reverse ++ m.d}.stk⟩ := by
  intro L
  induction L with
  | nil =>
      intro _ m v h
      refine ⟨true, ?_⟩
      have e : ({m with e := [], d := [].reverse ++ m.d} : MS) = m := by
        obtain ⟨⟩ := m; simp only at h; subst h; rfl
      rw [e]
      exact back_nil m v h
  | cons s L ih =>
      intro hL m v h
      obtain ⟨v₁, r₁⟩ := back_step m v s (hL s (by simp)) L h
      obtain ⟨v₂, r₂⟩ := ih (fun x hx => hL x (by simp [hx])) {m with e := L, d := s :: m.d} v₁
        rfl
      exact ⟨v₂, run_cast (r₁.trans r₂) (by simp only [List.length_cons]; omega) (by simp)⟩

/-- Put the current occurrence on `D`: its literal vertex (a copy of `N`), its name (through
`B`) and its polarity marker. -/
theorem put_run (x : ℕ) (b : Bool) (hA : m.a = name x) (hP : m.p = [.lit b]) :
    ∃ v', Run prog (2 * m.n + 2 * (encodeNat x).length + 5) ⟨some .putN, v, m.stk⟩
      ⟨some .aft, v', {m with a := [], p := [], d := dTok (x, b, m.n, m.n + 1) ++ m.d}.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := dup_run .n (c := .D) Sym.cl (by decide) (by decide) (l₁ := .putN)
    (l₂ := .putW) (next := .putA) rfl rfl m.n v m.stk rfl rfl
  rw [show update m.stk .D (cnt (Sym.cl : Γ .D) m.n ++ m.stk .D) =
    {m with d := cnt Sym.cl m.n ++ m.d}.stk from upd_D _ _] at r₁
  obtain ⟨v₂, S₂, r₂, h2A, h2B, h2k⟩ := moveB_run (M := prog) (self := .putA) (next := .putB)
    (a := .A) (b := .B) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) (encodeNat x) (name x)
    [] v₁ {m with d := cnt Sym.cl m.n ++ m.d}.stk (by simp [hA]) (isBitBlock_map _) rfl
  obtain ⟨v₃, S₃, r₃, h3B, h3D, h3k⟩ := moveB_run (M := prog) (self := .putB) (next := .putP)
    (a := .B) (b := .D) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) (encodeNat x).reverse
    (name x).reverse [] v₂ S₂ (by simp [h2B]) (isBitBlock_map_reverse _) rfl
  have hS₃ : S₃ = {m with a := [], d := name x ++ cnt Sym.cl m.n ++ m.d}.stk := by
    funext k; cases k <;> simp [h3B, h3D, h3k, h2A, h2k, List.map_reverse]
  rw [hS₃] at r₃
  have r₄ := putP_step {m with a := [], d := name x ++ cnt Sym.cl m.n ++ m.d} v₃ b (by simp [hP])
  exact ⟨b, run_cast (((r₁.trans r₂).trans r₃).trans r₄) (by simp only [List.length_reverse]; omega)
    (by simp [dTok])⟩

end Phases

/-! ### The edges of the site runs -/

/-- The occurrence triangle: `(L, M)`, `(L, 2)`, `(M, 2)` with `L = N`, `M = N + 1`. -/
def occSites : List Site := [.o1, .o2, .o3, .o4]

/-- The consistency edges with an earlier occurrence (`L'` on `U`): equal (`true`) or opposite
polarity. -/
def consSites (b : Bool) : List Site :=
  if b then [.c1, .c2, .c3, .c4] else [.d1, .d2, .d3, .d4]

/-- The OR gadget with inputs `N` and `R` and fresh vertices `N + 2`, `N + 3`, `N + 4`. -/
def orSites : List Site := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The clause end: the output `R` joined to `F` and `B`. -/
def endSites : List Site := [.e1, .e2]

/-- The empty clause: the vertex `N` joined to the palette. -/
def empSites : List Site := [.z1, .z2, .z3]

theorem out_cons (e : ℕ × ℕ) (es : List (ℕ × ℕ)) : out (e :: es) = out es ++ eB e := by
  simp [out]

@[simp] theorem out_nil : out [] = [] := rfl

theorem occ_out (m : MS) :
    chainOut m occSites = out [(m.n, m.n + 1), (m.n, 2), (m.n + 1, 2)] := by
  simp [occSites, atom, Site.src, Site.top, MS.val, out_cons, eB, List.replicate_succ']

theorem cons_out (b : Bool) (m : MS) : chainOut m (consSites b) =
    out (if b then [(m.u, m.n + 1), (m.u + 1, m.n)] else [(m.u, m.n), (m.u + 1, m.n + 1)]) := by
  cases b <;> simp [consSites, atom, Site.src, Site.top, MS.val, out_cons, eB,
    List.replicate_succ']

theorem or_out (m : MS) : chainOut m orSites = out [(m.n, m.n + 2), (m.r, m.n + 3),
    (m.n + 2, m.n + 3), (m.n + 2, m.n + 4), (m.n + 3, m.n + 4), (m.n + 4, 2)] := by
  simp [orSites, atom, Site.src, Site.top, MS.val, out_cons, eB, List.replicate_add]

theorem end_out (m : MS) : chainOut m endSites = out [(m.r, 1), (m.r, 2)] := by
  simp [endSites, atom, Site.src, Site.top, MS.val, out_cons, eB]

theorem emp_out (m : MS) : chainOut m empSites = out [(m.n, 0), (m.n, 1), (m.n, 2)] := by
  simp [empSites, atom, Site.src, Site.top, MS.val, out_cons, eB]

/-! ### The walk over earlier occurrences -/

theorem consEdges_same (x : ℕ) (p b : Bool) (L' n : ℕ) :
    consEdges (x, p) n (n + 1) (x, b, L', L' + 1) =
      if b == p then [(L', n + 1), (L' + 1, n)] else [(L', n), (L' + 1, n + 1)] := by
  cases b <;> cases p <;> simp [consEdges]

theorem flatMap_dTok_head (qs : List (ℕ × Bool × ℕ × ℕ)) :
    (qs.flatMap dTok).head?.bind unitOf = none ∧ (qs.flatMap dTok).head?.bind Sym.bit? = none := by
  cases qs with
  | nil => exact ⟨rfl, rfl⟩
  | cons q qs => simp [List.flatMap_cons, dTok, unitOf, Sym.bit?]

theorem isTok_dTok (qs : List (ℕ × Bool × ℕ × ℕ)) :
    ∀ s ∈ (qs.flatMap dTok).reverse, isTok s = true := by
  intro s hs
  simp only [List.mem_reverse, List.mem_flatMap, dTok, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_replicate] at hs
  obtain ⟨q, -, hs⟩ := hs
  rcases hs with rfl | ⟨b, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- One earlier occurrence `q` on `D`, for the new occurrence `l` (its name on `A`, its polarity
on `P`): push the consistency edges and move `q` to `E`. -/
theorem ent_run (l : ℕ × Bool) (q : ℕ × Bool × ℕ × ℕ) (hq : q.2.2.2 = q.2.2.1 + 1)
    (R : List Sym) (hR : R.head?.bind unitOf = none) (hRb : R.head?.bind Sym.bit? = none)
    (m : MS) (v : Bool) (hD : m.d = dTok q ++ R) (hA : m.a = name l.1) (hP : m.p = [.lit l.2])
    (hU : m.u = 0) :
    ∃ v', RunLe prog (12 * (dTok q).length + 8 * (m.n + m.r) + 21) ⟨some .walk, v, m.stk⟩
      ⟨some .walk, v', {m with
        d := R, e := (dTok q).reverse ++ m.e,
        o := out (consEdges l m.n (m.n + 1) q) ++ m.o}.stk⟩ := by
  obtain ⟨x', b', L', M'⟩ := q
  obtain ⟨x, p⟩ := l
  simp only at hq hA hP ⊢
  subst hq
  have hD' : m.d = .lit b' :: (name x' ++ (cnt Sym.cl L' ++ R)) := by simp [hD, dTok]
  have r₁ := walk_lit m v b' _ hD'
  have hcR : (cnt Sym.cl L' ++ R).head?.bind Sym.bit? = none := by
    cases L' <;> simp [Sym.bit?, hRb, List.replicate_succ]
  obtain ⟨v₂, r₂⟩ := cmp_run {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e}
    b' (encodeNat x) (encodeNat x') _ hcR hA rfl
  have hlen : (dTok (x', b', L', L' + 1)).length = (encodeNat x').length + L' + 1 := by
    simp [dTok]
  by_cases hx : x' = x
  · subst hx
    rw [show (if encodeNat x' = encodeNat x' then Lab.sel else .mvN none) = .sel by simp] at r₂
    have r₃ := sel_step {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e} v₂ b' p
      m.e rfl hP
    obtain ⟨v₄, r₄⟩ := mvN_run {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e}
      (b' == p) (some (b' == p)) (encodeNat x') _ hcR rfl
    obtain ⟨v₅, r₅⟩ := mvU_run {m with
      d := cnt Sym.cl L' ++ R, e := (name x').reverse ++ .lit b' :: m.e} v₄ (b' == p) L' R hR rfl
      hU
    obtain ⟨v₆, r₆⟩ := chain_run (consSites (b' == p)) {m with
      d := R, e := (name x').reverse ++ .lit b' :: m.e, u := L'}
      (.pre (if b' == p then .c1 else .d1)) .dr (by cases b' <;> cases p <;> decide) v₅
    obtain ⟨v₇, r₇⟩ := dr_run {m with
      d := R, e := (name x').reverse ++ .lit b' :: m.e, u := L',
      o := chainOut {m with d := R, e := (name x').reverse ++ .lit b' :: m.e, u := L'}
        (consSites (b' == p)) ++ m.o} v₆
    refine ⟨v₇, runLe_cast ((((r₁.le le_rfl).trans r₂).trans
      (((r₃.trans r₄).trans r₅).le le_rfl)).trans r₆ |>.trans (r₇.le le_rfl)) ?_ ?_⟩
    · have h4 : (consSites (b' == p)).length = 4 := by cases b' <;> cases p <;> rfl
      simp only [h4, hlen]
      omega
    · simp [cons_out, consEdges_same, dTok, hU]
  · have hne : encodeNat x ≠ encodeNat x' := fun h => hx (encodeNat_inj.1 h).symm
    rw [show (if encodeNat x = encodeNat x' then Lab.sel else .mvN none) = .mvN none by
      simp [hne]] at r₂
    obtain ⟨v₃, r₃⟩ := mvN_run {m with d := name x' ++ (cnt Sym.cl L' ++ R), e := .lit b' :: m.e}
      v₂ none (encodeNat x') _ hcR rfl
    obtain ⟨v₄, r₄⟩ := skU_run {m with
      d := cnt Sym.cl L' ++ R, e := (name x').reverse ++ .lit b' :: m.e} v₃ L' R hR rfl
    refine ⟨v₄, runLe_cast (((r₁.le le_rfl).trans r₂).trans ((r₃.trans r₄).le le_rfl)) ?_ ?_⟩
    · simp only [hlen]
      omega
    · simp [consEdges, hx, dTok]

/-- The walk over the earlier occurrences `qs` on `D`: push their consistency edges with `l`
and move `D` to `E`. -/
theorem walk_run (l : ℕ × Bool) : ∀ (qs : List (ℕ × Bool × ℕ × ℕ)),
    (∀ q ∈ qs, q.2.2.2 = q.2.2.1 + 1) → ∀ (m : MS) (v : Bool), m.d = qs.flatMap dTok →
    m.a = name l.1 → m.p = [.lit l.2] → m.u = 0 →
    ∃ v', RunLe prog (12 * (qs.flatMap dTok).length + qs.length * (8 * (m.n + m.r) + 21) + 1)
      ⟨some .walk, v, m.stk⟩ ⟨some .back, v', {m with
        d := [], e := (qs.flatMap dTok).reverse ++ m.e,
        o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++ m.o}.stk⟩ := by
  intro qs
  induction qs with
  | nil =>
      intro _ m v hD _ _ _
      refine ⟨true, runLe_cast ((walk_nil m v (by simpa using hD)).le le_rfl) (by simp) ?_⟩
      obtain ⟨⟩ := m
      simp only [List.flatMap_nil] at hD
      subst hD
      rfl
  | cons q qs ih =>
      intro hq m v hD hA hP hU
      obtain ⟨v₁, r₁⟩ := ent_run l q (hq q (by simp)) (qs.flatMap dTok) (flatMap_dTok_head qs).1
        (flatMap_dTok_head qs).2 m v (by simpa using hD) hA hP hU
      obtain ⟨v₂, r₂⟩ := ih (fun q' h => hq q' (by simp [h])) {m with
        d := qs.flatMap dTok, e := (dTok q).reverse ++ m.e,
        o := out (consEdges l m.n (m.n + 1) q) ++ m.o} v₁ rfl hA hP hU
      refine ⟨v₂, runLe_cast (r₁.trans r₂) ?_ ?_⟩
      · simp only [List.flatMap_cons, List.length_append, List.length_cons]
        nlinarith
      · simp [List.flatMap_cons, out_append]

/-- One literal occurrence `l`, from `lits`: push its triangle and its consistency edges with
the earlier occurrences `qs`, and put it on `D`. `N` is not advanced yet. -/
theorem occ_run (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (qs : List (ℕ × Bool × ℕ × ℕ)) (hq : ∀ q ∈ qs, q.2.2.2 = q.2.2.1 + 1) (m : MS) (v : Bool)
    (hT : m.t = Check.litRev l ++ R) (hD : m.d = qs.flatMap dTok) (hE : m.e = [])
    (hA : m.a = []) (hP : m.p = []) (hU : m.u = 0) :
    ∃ v', RunLe prog (13 * (qs.flatMap dTok).length + qs.length * (8 * (m.n + m.r) + 21) +
        10 * (m.n + m.r) + 3 * (encodeNat l.1).length + 30) ⟨some .lits, v, m.stk⟩
      ⟨some .aft, v', {m with
        t := R, d := ((l.1, l.2, m.n, m.n + 1) :: qs).flatMap dTok,
        o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++
          out [(m.n, m.n + 1), (m.n, 2), (m.n + 1, 2)] ++ m.o}.stk⟩ := by
  have hT' : m.t = .lit l.2 :: ((name l.1).reverse ++ R) := by simp [hT, Check.litRev]
  have r₁ := lits_lit m v (by simp [hT', isLit])
  obtain ⟨v₂, r₂⟩ := chain_run occSites m (.pre .o1) .lp (by decide) true
  have r₃ := lp_step {m with o := chainOut m occSites ++ m.o} v₂ l.2 _ hT'
  obtain ⟨v₄, r₄⟩ := nm_run {m with
    o := chainOut m occSites ++ m.o, t := (name l.1).reverse ++ R, p := .lit l.2 :: m.p} l.2 l.1
    R hR rfl hA
  obtain ⟨v₅, r₅⟩ := walk_run l qs hq {m with
    o := chainOut m occSites ++ m.o, t := R, p := .lit l.2 :: m.p, a := name l.1} v₄ hD rfl
    (by simp [hP]) hU
  obtain ⟨v₆, r₆⟩ := back_run (qs.flatMap dTok).reverse (isTok_dTok qs) {m with
      o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++ (chainOut m occSites ++ m.o),
      t := R, p := .lit l.2 :: m.p, a := name l.1, d := [],
      e := (qs.flatMap dTok).reverse ++ m.e} v₅ (by simp [hE])
  obtain ⟨v₇, r₇⟩ := put_run {m with
      o := out (qs.flatMap (consEdges l m.n (m.n + 1))) ++ (chainOut m occSites ++ m.o),
      t := R, p := .lit l.2 :: m.p, a := name l.1, d := (qs.flatMap dTok).reverse.reverse ++ [],
      e := []} v₆ l.1 l.2 rfl (by simp [hP])
  refine ⟨v₇, runLe_cast ((((r₁.le le_rfl).trans r₂).trans ((r₃.trans r₄).le le_rfl)).trans r₅
    |>.trans ((r₆.trans r₇).le le_rfl)) ?_ ?_⟩
  · simp only [occSites, List.length_cons, List.length_nil, List.length_reverse, hU]
    omega
  · simp [occ_out, hE, hA, hP, List.flatMap_cons, List.append_assoc]

/-! ### The size invariant -/

/-- The size invariant after `τ` tokens: the next vertex, the number and the total size of the
earlier occurrences are bounded, and each occurrence's negation vertex follows its literal
vertex. -/
def Inv (τ : ℕ) (s : ColSt) : Prop :=
  s.next ≤ 5 * τ + 3 ∧ s.prev.length ≤ τ ∧ (s.prev.flatMap dTok).length ≤ τ * (s.next + 1) ∧
    ∀ q ∈ s.prev, q.2.2.2 = q.2.2.1 + 1

theorem Inv.of_eq {τ : ℕ} {s s' : ColSt} (h : Inv τ s) (hn : s'.next = s.next)
    (hp : s'.prev = s.prev) : Inv τ s' := by
  unfold Inv; rw [hn, hp]; exact h

/-- A clause token adding at most five vertices keeps the invariant. -/
theorem Inv.bump {τ : ℕ} {s s' : ColSt} (h : Inv τ s) (hp : s'.prev = s.prev)
    (hn : s.next ≤ s'.next) (hn' : s'.next ≤ s.next + 5) : Inv (τ + 1) s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by rw [hp]; omega, ?_, by rw [hp]; exact h4⟩
  rw [hp]
  have : τ * (s.next + 1) ≤ (τ + 1) * (s'.next + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- A new occurrence of `l`, with at most five fresh vertices, keeps the invariant. -/
theorem Inv.occ {τ : ℕ} {s s' : ColSt} (l : ℕ × Bool) (h : Inv τ s)
    (hp : s'.prev = (l.1, l.2, s.next, s.next + 1) :: s.prev) (hn : s.next ≤ s'.next)
    (hn' : s'.next ≤ s.next + 5) : Inv (τ + (Check.litRev l).length) s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl := Check.litRev_length l
  refine ⟨by omega, by rw [hp, List.length_cons]; omega, ?_, ?_⟩
  · rw [hp, List.flatMap_cons, List.length_append]
    have hd : (dTok (l.1, l.2, s.next, s.next + 1)).length =
        (encodeNat l.1).length + s.next + 1 := by simp [dTok]
    rw [hd, hl]
    have e1 : τ * (s.next + 1) ≤ τ * (s'.next + 1) := Nat.mul_le_mul_left _ (by omega)
    have e2 : ((encodeNat l.1).length + 1) * (s.next + 1) ≤
        ((encodeNat l.1).length + 1) * (s'.next + 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · rw [hp]
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · rfl
    · exact h4 q hq

theorem inv_colLits : ∀ (ls : List (ℕ × Bool)) (o : ℕ) (s : ColSt) (τ : ℕ), Inv τ s →
    Inv (τ + (ls.flatMap Check.litRev).length) (colLits ls o s) := by
  intro ls
  induction ls with
  | nil =>
      intro o s τ h
      rw [List.flatMap_nil, List.length_nil, Nat.add_zero]
      exact h.of_eq rfl rfl
  | cons l ls ih =>
      intro o s τ h
      have h' := ih (colOr (colOcc l s).2 o (colOcc l s).1).2 _ _
        (h.occ l (s' := (colOr (colOcc l s).2 o (colOcc l s).1).1) rfl
        (by simp only [colOr, colOcc]; omega) (by simp only [colOr, colOcc]; omega))
      rw [List.flatMap_cons, List.length_append, ← Nat.add_assoc]
      exact h'

private theorem clRev_length' (C : CNFClause) :
    (Check.clRev C).length = (C.reverse.flatMap Check.litRev).length + 1 := by
  simp [Check.clRev]

theorem inv_colClause (C : CNFClause) (s : ColSt) (τ : ℕ) (h : Inv τ s) :
    Inv (τ + (Check.clRev C).length) (colClause C s) := by
  rw [clRev_length']
  unfold colClause
  cases hC : C.reverse with
  | nil => exact h.bump rfl (by simp) (by simp)
  | cons l ls =>
      have h1 := (h.bump (s' := s) rfl le_rfl (by omega)).occ l (s' := (colOcc l s).1) rfl
        (by simp only [colOcc]; omega) (by simp only [colOcc]; omega)
      have h2 := inv_colLits ls (colOcc l s).2 _ _ h1
      simp only [List.flatMap_cons, List.length_append] at h2 ⊢
      convert h2 using 1
      omega

theorem inv_foldl : ∀ (Cs : CNF) (s : ColSt) (τ : ℕ), Inv τ s →
    Inv (τ + (Cs.flatMap Check.clRev).length) (Cs.foldl (fun s C => colClause C s) s) := by
  intro Cs
  induction Cs with
  | nil => intro s τ h; simpa using h
  | cons C Cs ih =>
      intro s τ h
      have := ih _ _ (inv_colClause C s τ h)
      rw [List.flatMap_cons, List.length_append, ← Nat.add_assoc]
      exact this

/-! ### Literals, clauses, the formula -/

/-- The step budget per token, for formulas of at most `Lb` tokens. -/
def budget (Lb : ℕ) : ℕ := 400 * (Lb + 1) ^ 2

/-- The quiescent state of the construction state `s`: tokens `t`, the output above `o0`, the
OR output `r` and the first-literal flag `f`. -/
def enc (s : ColSt) (t : List Sym) (o0 : List Bool) (r f : ℕ) : MS :=
  ⟨t, out s.em ++ o0, s.next, r, s.prev.flatMap dTok, [], [], [], f, 0⟩

theorem runLe_cast' {k k' : ℕ} {c c' d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog k c d)
    (hc : c' = c) (hk : k ≤ k') (hd : d = d') : RunLe prog k' c' d' := hc ▸ hd ▸ h.mono hk

/-- The cost of one literal, under the size invariant. -/
theorem lit_cost {Lb τ n r P D w : ℕ} (hτ : τ + w + 1 ≤ Lb) (hn : n ≤ 5 * τ + 3) (hr : r ≤ n)
    (hP : P ≤ τ) (hD : D ≤ τ * (n + 1)) :
    13 * D + P * (8 * (n + r) + 21) + 40 * (n + r) + 3 * w + 100 ≤ budget Lb := by
  unfold budget
  have h1 : P * (8 * (n + r) + 21) ≤ Lb * (16 * (5 * Lb + 3) + 21) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : τ * (n + 1) ≤ Lb * (5 * Lb + 4) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem headLit_of (R : List Sym) (hR : R = [] ∨ R.head? = some .cl) :
    isLit R.head? = false ∧ R.head?.bind Sym.bit? = none := by
  rcases hR with rfl | h <;> simp [isLit, Sym.bit?, *]

theorem flatMap_litRev_head (ls : List (ℕ × Bool)) (R : List Sym)
    (hR : R.head?.bind Sym.bit? = none) :
    (ls.flatMap Check.litRev ++ R).head?.bind Sym.bit? = none := by
  cases ls with
  | nil => simpa using hR
  | cons l ls => simp [List.flatMap_cons, Check.litRev, Sym.bit?]

/-- The remaining literals `ls` of a clause, from `lits` with the OR output `o` on `R`: per
literal its occurrence, OR gadget and counter update; then the clause end. -/
theorem lits_run (Lb : ℕ) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl) (o0 : List Bool) :
    ∀ (ls : List (ℕ × Bool)) (o : ℕ) (s : ColSt) (τ : ℕ) (v : Bool), Inv τ s → o ≤ s.next →
      τ + (ls.flatMap Check.litRev).length ≤ Lb →
      ∃ v', RunLe prog (((ls.flatMap Check.litRev).length + 1) * budget Lb)
        ⟨some .lits, v, (enc s (ls.flatMap Check.litRev ++ R) o0 o 0).stk⟩
        ⟨some .cls, v', (enc (colLits ls o s) R o0 0 0).stk⟩ := by
  obtain ⟨hRl, hRb⟩ := headLit_of R hR
  intro ls
  induction ls with
  | nil =>
      intro o s τ v hinv ho hb
      have r₁ := lits_end (enc s R o0 o 0) v hRl
      obtain ⟨v₂, r₂⟩ := chain_run endSites (enc s R o0 o 0) (.pre .e1) (.clr false) (by decide)
        false
      obtain ⟨v₃, r₃⟩ := clr_run {enc s R o0 o 0 with
        o := chainOut (enc s R o0 o 0) endSites ++ (enc s R o0 o 0).o} v₂ false
      refine ⟨v₃, runLe_cast (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)) ?_ ?_⟩
      · have h1 := hinv.1
        simp only [enc, endSites, List.length_cons, List.length_nil, List.flatMap_nil, budget]
        nlinarith
      · simp [enc, colLits, end_out, out_append]
  | cons l ls ih =>
      intro o s τ v hinv ho hb
      have hl := Check.litRev_length l
      simp only [List.flatMap_cons, List.length_append] at hb ⊢
      rw [List.append_assoc]
      obtain ⟨v₁, r₁⟩ := occ_run l (ls.flatMap Check.litRev ++ R) (flatMap_litRev_head ls R hRb)
        s.prev hinv.2.2.2 (enc s (Check.litRev l ++ (ls.flatMap Check.litRev ++ R)) o0 o 0) v rfl
        rfl rfl rfl rfl rfl
      let m₁ : MS := ⟨ls.flatMap Check.litRev ++ R,
        out (s.prev.flatMap (consEdges l s.next (s.next + 1))) ++
          out [(s.next, s.next + 1), (s.next, 2), (s.next + 1, 2)] ++ (out s.em ++ o0),
        s.next, o, ((l.1, l.2, s.next, s.next + 1) :: s.prev).flatMap dTok, [], [], [], 0, 0⟩
      obtain ⟨v₂, r₂⟩ := aft_zero m₁ v₁ rfl
      obtain ⟨v₃, r₃⟩ := chain_run orSites m₁ (.pre .r1) (.clr true) (by decide) v₂
      obtain ⟨v₄, r₄⟩ := clr_run {m₁ with o := chainOut m₁ orSites ++ m₁.o} v₃ true
      obtain ⟨v₅, r₅⟩ := fAB_run {m₁ with o := chainOut m₁ orSites ++ m₁.o, r := 0} v₄ false
      have r₆ := fC_step {m₁ with o := chainOut m₁ orSites ++ m₁.o, r := s.next + 0} v₅ false
      let r' := colOr (colOcc l s).2 o (colOcc l s).1
      obtain ⟨v₇, r₇⟩ := ih r'.2 r'.1 (τ + (Check.litRev l).length) v₅
        (hinv.occ l rfl (by simp only [r', colOr, colOcc]; omega)
          (by simp only [r', colOr, colOcc]; omega))
        (by simp only [r', colOr, colOcc]; omega) (by omega)
      have hmid : (⟨some .lits, v₅, {m₁ with
          o := chainOut m₁ orSites ++ m₁.o, r := s.next + 0 + (if false then 0 else 4),
          n := s.next + (if false then 2 else 5)}.stk⟩ : TM2.Cfg Γ Lab Bool) =
          ⟨some .lits, v₅, (enc r'.1 (ls.flatMap Check.litRev ++ R) o0 r'.2 0).stk⟩ := by
        simp [m₁, r', enc, colOr, colOcc, or_out, out_append, out_cons, Nat.add_assoc]
      refine ⟨v₇, runLe_cast ((((r₁.trans (r₂.le le_rfl)).trans r₃).trans
        (((r₄.trans r₅).trans r₆).le le_rfl)).trans (runLe_cast' r₇ hmid le_rfl rfl)) ?_ rfl⟩
      have hc := lit_cost (Lb := Lb) (w := (encodeNat l.1).length) (by omega) hinv.1 ho hinv.2.1
        hinv.2.2.1
      have hK : budget Lb ≤ (Check.litRev l).length * budget Lb :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [enc, m₁, orSites, List.length_cons, List.length_nil]
      nlinarith

/-- One clause `C`, from `cls` with its tokens `clRev C` on `T`. -/
theorem clause_run (Lb : ℕ) (C : CNFClause) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl)
    (o0 : List Bool) (s : ColSt) (τ : ℕ) (v : Bool) (hinv : Inv τ s)
    (hb : τ + (Check.clRev C).length ≤ Lb) :
    ∃ v', RunLe prog ((Check.clRev C).length * (budget Lb + 1))
      ⟨some .cls, v, (enc s (Check.clRev C ++ R) o0 0 0).stk⟩
      ⟨some .cls, v', (enc (colClause C s) R o0 0 0).stk⟩ := by
  obtain ⟨hRl, hRb⟩ := headLit_of R hR
  have hcl : Check.clRev C ++ R = .cl :: (C.reverse.flatMap Check.litRev ++ R) := by
    simp [Check.clRev]
  rw [hcl, clRev_length']
  rw [clRev_length'] at hb
  unfold colClause
  cases hC : C.reverse with
  | nil =>
      rw [hC] at hb
      have r₁ := cls_emp (enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0) v R rfl hRl
      obtain ⟨v₂, r₂⟩ := chain_run empSites
        {enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0 with t := R} (.pre .z1) .zN
        (by decide) false
      have r₃ := zN_step {enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0 with
        t := R,
        o := chainOut {enc s (.cl :: ([].flatMap Check.litRev ++ R)) o0 0 0 with t := R}
          empSites ++ (out s.em ++ o0)} v₂
      refine ⟨v₂, runLe_cast (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)) ?_ ?_⟩
      · have h1 := hinv.1
        simp only [enc, empSites, List.length_cons, List.length_nil, List.flatMap_nil, budget]
        nlinarith
      · simp [enc, emp_out, out_append]
  | cons l ls =>
      rw [hC] at hb
      have hl := Check.litRev_length l
      simp only [List.flatMap_cons, List.length_append] at hb ⊢
      rw [List.append_assoc]
      have r₁ := cls_lit (enc s (.cl :: (Check.litRev l ++ (ls.flatMap Check.litRev ++ R))) o0 0 0)
        v _ rfl (by simp [Check.litRev, isLit])
      obtain ⟨v₂, r₂⟩ := occ_run l (ls.flatMap Check.litRev ++ R) (flatMap_litRev_head ls R hRb)
        s.prev hinv.2.2.2 {enc s (.cl :: (Check.litRev l ++ (ls.flatMap Check.litRev ++ R))) o0 0 0
          with t := Check.litRev l ++ (ls.flatMap Check.litRev ++ R), f := 0 + 1} true rfl rfl rfl
        rfl rfl rfl
      let m₂ : MS := ⟨ls.flatMap Check.litRev ++ R,
        out (s.prev.flatMap (consEdges l s.next (s.next + 1))) ++
          out [(s.next, s.next + 1), (s.next, 2), (s.next + 1, 2)] ++ (out s.em ++ o0),
        s.next, 0, ((l.1, l.2, s.next, s.next + 1) :: s.prev).flatMap dTok, [], [], [], 0 + 1, 0⟩
      obtain ⟨v₃, r₃⟩ := aft_pos m₂ v₂ rfl
      obtain ⟨v₄, r₄⟩ := fAB_run {m₂ with f := 0} v₃ true
      have r₅ := fC_step {m₂ with f := 0, r := s.next + 0} v₄ true
      obtain ⟨v₆, r₆⟩ := lits_run Lb R hR o0 ls (colOcc l s).2 (colOcc l s).1
        (τ + 1 + (Check.litRev l).length) v₄
        ((hinv.bump (s' := s) rfl le_rfl (by omega)).occ l rfl (by simp only [colOcc]; omega)
          (by simp only [colOcc]; omega))
        (by simp only [colOcc]; omega) (by omega)
      have hmid : (⟨some .lits, v₄, {m₂ with
          f := 0, r := s.next + 0 + (if true then 0 else 4),
          n := s.next + (if true then 2 else 5)}.stk⟩ : TM2.Cfg Γ Lab Bool) =
          ⟨some .lits, v₄, (enc (colOcc l s).1 (ls.flatMap Check.litRev ++ R) o0
            (colOcc l s).2 0).stk⟩ := by
        simp [m₂, enc, colOcc, out_append, out_cons]
      refine ⟨v₆, runLe_cast ((((r₁.le le_rfl).trans r₂).trans
        (((r₃.trans r₄).trans r₅).le le_rfl)).trans (runLe_cast' r₆ hmid le_rfl rfl)) ?_ rfl⟩
      have hc := lit_cost (Lb := Lb) (r := 0) (w := (encodeNat l.1).length) (by omega) hinv.1
        (Nat.zero_le _) hinv.2.1 hinv.2.2.1
      have hK : budget Lb ≤ (Check.litRev l).length * budget Lb :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [enc]
      nlinarith

/-- The clauses `Cs`, from `cls` with their tokens on `T`. -/
theorem formula_run (Lb : ℕ) (o0 : List Bool) : ∀ (Cs : CNF) (s : ColSt) (τ : ℕ) (v : Bool),
    Inv τ s → τ + (Cs.flatMap Check.clRev).length ≤ Lb →
    ∃ v', RunLe prog ((Cs.flatMap Check.clRev).length * (budget Lb + 1))
      ⟨some .cls, v, (enc s (Cs.flatMap Check.clRev) o0 0 0).stk⟩
      ⟨some .cls, v', (enc (Cs.foldl (fun s C => colClause C s) s) [] o0 0 0).stk⟩ := by
  intro Cs
  induction Cs with
  | nil => intro s τ v _ _; exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) rfl⟩
  | cons C Cs ih =>
      intro s τ v hinv hb
      have hR : Cs.flatMap Check.clRev = [] ∨ (Cs.flatMap Check.clRev).head? = some .cl := by
        cases Cs with
        | nil => left; rfl
        | cons C' Cs' => right; simp [List.flatMap_cons, Check.clRev]
      simp only [List.flatMap_cons, List.length_append] at hb
      obtain ⟨v₁, r₁⟩ := clause_run Lb C (Cs.flatMap Check.clRev) hR o0 s τ v hinv (by omega)
      obtain ⟨v₂, r₂⟩ := ih (colClause C s) (τ + (Check.clRev C).length) v₁
        (inv_colClause C s τ hinv) (by omega)
      refine ⟨v₂, runLe_cast (r₁.trans r₂) (by simp [List.flatMap_cons, add_mul]) rfl⟩

/-! ### The emitter -/

/-- **The emitter.** From `start`, with the token stack `(toks φ).reverse`, the output stack `o`
and every other stack empty, the machine reaches `done` within `500 (|toks φ| + 1)⁴` steps
with the 3-COLOR instance `toCol φ` pushed on the output stack (read top-first). -/
theorem run (φ : CNF) (o : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hT : St .T = (toks φ).reverse) (hO : St .O = o) (h0 : ∀ k, k ≠ .T → k ≠ .O → St k = []) :
    ∃ v' S', RunLe prog (500 * ((toks φ).length + 1) ^ 4) ⟨some start, v, St⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = toCol φ ++ o := by
  have hSt : St = (MS.mk (toks φ).reverse o 0 0 [] [] [] [] 0 0).stk := by
    funext k
    cases k
    · exact hT
    · exact hO
    all_goals exact h0 _ (by decide) (by decide)
  set L := (toks φ).length with hL
  let s0 : ColSt := ⟨3, [], [(0, 1), (0, 2), (1, 2)]⟩
  have hinv0 : Inv 0 s0 := by simp [Inv, s0]
  have hTr : (toks φ).reverse = φ.reverse.flatMap Check.clRev := Check.toks_reverse φ
  have hL' : (φ.reverse.flatMap Check.clRev).length = L := by rw [← hTr, List.length_reverse]
  have r₁ := init_step (MS.mk (toks φ).reverse o 0 0 [] [] [] [] 0 0) v
  obtain ⟨v₂, r₂⟩ := formula_run L o φ.reverse s0 0 v hinv0 (by omega)
  have hfin := (inv_foldl φ.reverse s0 0 hinv0).1
  have r₃ := cls_nil (enc (colSt φ) [] o 0 0) v₂ rfl
  obtain ⟨v₄, r₄⟩ := site_run .fin (enc (colSt φ) [] o 0 0) true
  refine ⟨v₄, {enc (colSt φ) [] o 0 0 with
    o := atom (enc (colSt φ) [] o 0 0) .fin ++ (enc (colSt φ) [] o 0 0).o}.stk, ?_, ?_⟩
  · rw [hSt]
    refine runLe_cast (((r₁.le le_rfl).trans (runLe_cast' r₂ ?_ le_rfl rfl)).trans
      ((r₃.trans r₄).le le_rfl)) ?_ rfl
    · simp [enc, s0, pal, hTr]
    · rw [hL'] at hfin
      change (colSt φ).next ≤ 5 * (0 + L) + 3 at hfin
      simp only [enc, MS.val, Site.src, budget, hL'] at hfin ⊢
      have h3 : (L + 1) ^ 3 ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : L + 1 ≤ (L + 1) ^ 4 := by
        calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
          _ ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : L * (400 * (L + 1) ^ 2 + 1) ≤ 400 * (L + 1) ^ 3 + L := by
        have : L * (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by
          calc L * (L + 1) ^ 2 ≤ (L + 1) * (L + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)
            _ = (L + 1) ^ 3 := by rw [pow_succ (L + 1) 2, Nat.mul_comm]
        nlinarith
      nlinarith
  · simp [enc, atom, MS.val, Site.src, Site.top, toCol_eq]

end Cslib.Complexity.Karp.EmitColor
