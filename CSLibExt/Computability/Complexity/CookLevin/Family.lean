/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `D3Fam.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/D3Fam.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, manual `Fintype` instances for enumeration types (`deriving Fintype` fails on them at
the pinned Mathlib); the stacks, the counter view and the multiplication site come from
`CounterView` instead of a specialized copy; module docstring rewritten for this repository (the
source's notes and status lines dropped), missing docstrings added, long lines wrapped.
-/

module

public import Mathlib.Tactic.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Computability.Encoding
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import MathlibExt.Computability.TuringMachine.Program
public import CSLibExt.Computability.Complexity.DenseSAT
public import CSLibExt.Computability.Complexity.CookLevin.CounterView

/-!
# Cook-Levin: generator machine for the transition clause families

For a verifier machine described by situation tables, the Cook-Levin formula contains, for every
time `t < T` and every situation number `i < N`, the clause

  `¬X[t, la i] ∨ ⋁_{k < KK, j < d} ¬C[t, k, j, wa i k j] ∨ X[t+1, na i]`

saying that situation `i` at time `t` forces the next label/state code `na i`. Instantiated with
the next-code table it is the update family; instantiated with the situation-variable table it is
the situation-definition family. Each clause is a *dense* clause over all `V = (T+1)·W` variables
(`Layout`), encoded with `DenseSAT.encodeCNF`.

This file defines the variable layout and the family (`family`), a counter machine `prog` that
emits `encodeCNF (family …)`, and its exact run and polynomial step bound (`gen_time`, `genC`).
The verifier-derived sizes and tables are parameters; `T` and `H` (time and height bounds) are
runtime inputs in unary.

The machine works in the shared counter view `CounterView` with counters `CK`
(`GK = SK CK`).
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Family

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.CounterView

/-! ## Draft C3 variable layout -/

/-- Constant sizes derived from the verifier. -/
structure Layout where
  /-- Size of the label/state block of a row. -/
  A : ℕ
  /-- Number of stacks. -/
  KK : ℕ
  /-- Number of symbol codes (code `0` is the empty cell). -/
  g : ℕ
  /-- Window depth. -/
  d : ℕ

namespace Layout

variable (L : Layout)

/-- Variables per time step: the label/state block, then `KK · H · g` cell variables. -/
def rowW (H : ℕ) : ℕ := L.A + L.KK * (H * L.g)

/-- Number of variables `V = (T + 1) · W`. -/
def numVars (T H : ℕ) : ℕ := (T + 1) * L.rowW H

/-- Label/state variable `a < A` at time `t`. -/
def xIdx (H t a : ℕ) : ℕ := t * L.rowW H + a

/-- Cell variable: stack `k`, depth `j < H` from the top, symbol code `x < g`, time `t`. -/
def cIdx (H t k j x : ℕ) : ℕ := t * L.rowW H + L.A + (k * H + j) * L.g + x

/-- Number of literals in a label-transition clause. -/
def nLits : ℕ := L.KK * L.d + 2

end Layout

/-! ## The clause family (pure specification) -/

section Spec

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ)

/-- Position of literal `j` of clause `(t, i)`: `j = 0` the current label, `1 ≤ j ≤ KK·d` the
window cells in `(k, j)`-lexicographic order, `j = KK·d + 1` the next label. -/
def litPos (H t i j : ℕ) : ℕ :=
  if j = 0 then L.xIdx H t (la i)
  else if j ≤ L.KK * L.d then
    L.cIdx H t ((j - 1) / L.d) ((j - 1) % L.d) (wa i ((j - 1) / L.d) ((j - 1) % L.d))
  else L.xIdx H (t + 1) (na i)

/-- Literals of clause `(t, i)`: all negative except the last (next label). -/
def lits (H t i : ℕ) : List (ℕ × Bool) :=
  (List.range L.nLits).map fun j => (litPos L la na wa H t i j, decide (j = L.nLits - 1))

/-- Dense clause over `V` variables with the given literals (slot `v` = `lits.lookup v`). -/
def denseClause (V : ℕ) (ls : List (ℕ × Bool)) : Clause :=
  (List.range V).map fun v => ls.lookup v

/-- The family: clauses ordered by time, then situation. -/
def family (T H N : ℕ) : CNF :=
  (List.range T).flatMap fun t =>
    (List.range N).map fun i => denseClause (L.numVars T H) (lits L la na wa H t i)

end Spec

/-! ## Block decomposition of a dense clause -/

/-- Encoding of the slots `lo, …, V-1` of a dense clause whose literals (all at positions `≥ lo`)
are `ls`: gaps of absent slots (`01`) between literal slots. -/
def gapEnc : ℕ → List (ℕ × Bool) → ℕ → List Bool
  | lo, [], V => rep [false, true] (V - lo)
  | lo, (p, b) :: r, V => rep [false, true] (p - lo) ++ encodeSlot (some b) ++ gapEnc (p + 1) r V

/-- Literal positions strictly increasing, starting at `≥ lo`, all `< V`. -/
def Inc : ℕ → List (ℕ × Bool) → ℕ → Prop
  | lo, [], V => lo ≤ V
  | lo, (p, _) :: r, V => lo ≤ p ∧ Inc (p + 1) r V

theorem Inc.le : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Inc lo ls V → lo ≤ V
  | _, [], _, h => h
  | _, (_, _) :: _, _, ⟨h1, h2⟩ => by have := Inc.le h2; omega

theorem lookup_cons_ne {p i : ℕ} {b : Bool} {r : List (ℕ × Bool)} (h : i ≠ p) :
    ((p, b) :: r).lookup i = r.lookup i := by
  have : (i == p) = false := beq_eq_false_iff_ne.mpr h
  rw [List.lookup_cons, this]

/-- Lowering the lower bound keeps a literal list increasing. -/
theorem Inc.mono_lo {lo lo' : ℕ} {ls : List (ℕ × Bool)} {V : ℕ} (h : lo' ≤ lo) (hi : Inc lo ls V) :
    Inc lo' ls V := by
  cases ls with
  | nil => exact le_trans h hi
  | cons pb r => obtain ⟨p, b⟩ := pb; exact ⟨le_trans h hi.1, hi.2⟩

theorem Inc.lookup_none : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Inc lo ls V →
    ∀ i, i < lo → ls.lookup i = none
  | _, [], _, _, _, _ => rfl
  | _, (_, _) :: _, _, ⟨h1, h2⟩, i, hi => by
      rw [lookup_cons_ne (by omega)]; exact Inc.lookup_none h2 i (by omega)

theorem flatMap_none {l : List ℕ} {f : ℕ → Option Bool} (h : ∀ i ∈ l, f i = none) :
    (l.map f).flatMap encodeSlot = rep [false, true] l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_cons, rep_succ]
      rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]
      rfl

theorem gapEnc_eq : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Inc lo ls V →
    ((List.range' lo (V - lo)).map fun v => ls.lookup v).flatMap encodeSlot = gapEnc lo ls V
  | lo, [], V, _ => by
      rw [flatMap_none (f := fun v => List.lookup v []) (fun _ _ => rfl), List.length_range']; rfl
  | lo, (p, b) :: r, V, ⟨h1, h2⟩ => by
      have hV := Inc.le h2
      have hsplit : List.range' lo (V - lo) =
          List.range' lo (p - lo) ++ (p :: List.range' (p + 1) (V - (p + 1))) := by
        rw [show V - lo = (p - lo) + (V - (p + 1) + 1) by omega, ← List.range'_append,
          show lo + 1 * (p - lo) = p by omega]
        rfl
      rw [hsplit, List.map_append, List.flatMap_append, List.map_cons, List.flatMap_cons,
        gapEnc, flatMap_none, List.length_range']
      · have hp : ((p, b) :: r).lookup p = some b := by simp
        have hm : (List.range' (p + 1) (V - (p + 1))).map (fun v => ((p, b) :: r).lookup v) =
            (List.range' (p + 1) (V - (p + 1))).map (fun v => r.lookup v) := by
          refine List.map_congr_left fun v hv => ?_
          rw [List.mem_range'_1] at hv
          exact lookup_cons_ne (by omega)
        rw [hp, hm, gapEnc_eq h2]
        simp [List.append_assoc]
      · intro v hv
        rw [List.mem_range'_1] at hv
        rw [lookup_cons_ne (by omega)]
        exact Inc.lookup_none h2 v (by omega)

/-- A dense clause with increasing literals encodes as its gap/literal blocks. -/
theorem encodeClause_denseClause {ls : List (ℕ × Bool)} {V : ℕ} (h : Inc 0 ls V) :
    encodeClause (denseClause V ls) = gapEnc 0 ls V ++ [false, false] := by
  rw [encodeClause, denseClause, List.range_eq_range', ← gapEnc_eq h]
  rfl

/-- Starting the gap encoding earlier just prepends absent slots. -/
theorem gapEnc_shift {lo lo' : ℕ} {ls : List (ℕ × Bool)} {V : ℕ} (hlo : lo ≤ lo')
    (h : Inc lo' ls V) : gapEnc lo ls V = rep [false, true] (lo' - lo) ++ gapEnc lo' ls V := by
  cases ls with
  | nil => simp only [gapEnc]; rw [← rep_add]; congr 1; have := Inc.le h; simp [Inc] at h; omega
  | cons pb r =>
      obtain ⟨p, b⟩ := pb
      obtain ⟨h1, -⟩ := h
      simp only [gapEnc, ← List.append_assoc, ← rep_add]
      congr 3; omega

/-! ## The literal positions are strictly increasing -/

theorem div_mod_succ_of_lt {c d : ℕ} (hd : 0 < d) (h : c % d + 1 < d) :
    (c + 1) / d = c / d ∧ (c + 1) % d = c % d + 1 := by
  have hc := Nat.div_add_mod c d
  have e : c + 1 = (c % d + 1) + d * (c / d) := by omega
  constructor
  · rw [e, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h, Nat.zero_add]
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem div_mod_succ_of_eq {c d : ℕ} (hd : 0 < d) (h : c % d + 1 = d) :
    (c + 1) / d = c / d + 1 ∧ (c + 1) % d = 0 := by
  have hc := Nat.div_add_mod c d
  have e : c + 1 = d * (c / d + 1) := by rw [Nat.mul_succ]; omega
  rw [e, Nat.mul_div_cancel_left _ hd, Nat.mul_mod_right]
  exact ⟨rfl, rfl⟩

/-- Generic: an increasing indexed family of literals satisfies `Inc`. -/
theorem inc_of_mono (f : ℕ → ℕ × Bool) (m V : ℕ)
    (hmono : ∀ j, j + 1 < m → (f j).1 < (f (j + 1)).1) (hlast : ∀ j, j + 1 = m → (f j).1 < V) :
    ∀ n a lo, a + n = m → (n = 0 → lo ≤ V) → (0 < n → lo ≤ (f a).1) →
      Inc lo ((List.range' a n).map f) V := by
  intro n
  induction n with
  | zero => intro a lo _ h0 _; exact h0 rfl
  | succ n ih =>
      intro a lo ham _ hpos
      refine ⟨hpos (Nat.succ_pos _), ih (a + 1) _ (by omega) (fun hn => ?_) (fun _ => ?_)⟩
      · exact hlast a (by omega)
      · exact hmono a (by omega)

section Sorted

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ)

/-- Well-formedness of the tables for situation `i` (codes in range, window within height). -/
structure WF (H i : ℕ) : Prop where
  la_lt : la i < L.A
  na_lt : na i < L.A
  wa_lt : ∀ k < L.KK, ∀ j < L.d, wa i k j < L.g
  d_le : L.d ≤ H

variable {L la na wa}

theorem cIdx_lt_next_row {H t k j x : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.cIdx H t k j x < (t + 1) * L.rowW H := by
  unfold Layout.cIdx Layout.rowW
  have h1 : (k * H + j) * L.g + x < (k * H + H) * L.g := by
    have : (k * H + j) * L.g + L.g ≤ (k * H + H) * L.g := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : (k * H + H) * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk)
  rw [Nat.succ_mul]; omega

theorem litPos_mono {H t i : ℕ} (hwf : WF L la na wa H i) (j : ℕ) (hj : j + 1 < L.nLits) :
    litPos L la na wa H t i j < litPos L la na wa H t i (j + 1) := by
  obtain ⟨hla, hna, hwa, hdH⟩ := hwf
  unfold Layout.nLits at hj
  have hW : L.A ≤ L.rowW H := Nat.le_add_right _ _
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- label literal → first cell (or next label if there are no cells)
    rw [litPos, litPos, ite_eq_left rfl, ite_eq_right (by omega : (0 : ℕ) + 1 ≠ 0)]
    split_ifs with h1
    · unfold Layout.xIdx Layout.cIdx; omega
    · unfold Layout.xIdx; rw [Nat.add_one_mul]; omega
  · have hd : 0 < L.d := Nat.pos_of_ne_zero fun h => by simp [h] at hj; omega
    have hcell : j ≤ L.KK * L.d := by omega
    simp only [litPos, ite_eq_right (show j ≠ 0 by omega), ite_eq_right (show j + 1 ≠ 0 by omega),
      ite_eq_left hcell, Nat.add_sub_cancel]
    have hq : (j - 1) / L.d < L.KK := by
      rw [Nat.div_lt_iff_lt_mul hd]; omega
    have hr : (j - 1) % L.d < L.d := Nat.mod_lt _ hd
    split_ifs with h2
    · -- cell → next cell
      have hc := Nat.div_add_mod (j - 1) L.d
      have hj' : j = j - 1 + 1 := by omega
      rcases Nat.lt_or_ge ((j - 1) % L.d + 1) L.d with h3 | h3
      · obtain ⟨e1, e2⟩ := div_mod_succ_of_lt hd h3
        rw [hj'] at e1 e2 ⊢
        simp only [Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        unfold Layout.cIdx
        have := hwa ((j - 1) / L.d) hq ((j - 1) % L.d) hr
        rw [show (j - 1) / L.d * H + ((j - 1) % L.d + 1) =
          (j - 1) / L.d * H + (j - 1) % L.d + 1 by omega, Nat.succ_mul]
        omega
      · obtain ⟨e1, e2⟩ := div_mod_succ_of_eq (c := j - 1) hd (by omega)
        rw [hj'] at e1 e2 ⊢
        simp only [Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        unfold Layout.cIdx
        have := hwa ((j - 1) / L.d) hq ((j - 1) % L.d) hr
        have hle : ((j - 1) / L.d * H + (j - 1) % L.d) * L.g + L.g ≤
            ((j - 1) / L.d + 1) * H * L.g := by
          rw [← Nat.succ_mul, Nat.succ_mul ((j - 1) / L.d)]
          exact Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_zero]; omega
    · -- last cell → next label
      unfold Layout.xIdx
      have := cIdx_lt_next_row (H := H) (t := t) hq (by omega : (j - 1) % L.d < H)
        (hwa ((j - 1) / L.d) hq ((j - 1) % L.d) hr)
      omega

theorem lits_inc {T H t i : ℕ} (ht : t < T) (hwf : WF L la na wa H i) :
    Inc 0 (lits L la na wa H t i) (L.numVars T H) := by
  unfold lits
  rw [List.range_eq_range']
  refine inc_of_mono _ L.nLits _ (fun j hj => litPos_mono hwf j hj) (fun j hj => ?_)
    L.nLits 0 0 (by omega) (by simp [Layout.nLits]) (fun _ => Nat.zero_le _)
  have hj : j = L.KK * L.d + 1 := by unfold Layout.nLits at hj; omega
  simp only [hj, litPos, Nat.add_one_ne_zero, ite_false,
    ite_eq_right (show ¬(L.KK * L.d + 1 ≤ L.KK * L.d) by omega)]
  unfold Layout.xIdx Layout.numVars
  have : na i < L.rowW H := lt_of_lt_of_le hwf.na_lt (Nat.le_add_right _ _)
  have : (t + 1 + 1) * L.rowW H ≤ (T + 1) * L.rowW H := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul (t + 1)] at this; omega

end Sorted

/-! ## The generator machine -/

/-- Unit-counter stacks of the generator. -/
inductive CK
  | Tn | Ti | Hs | Gc | HG | Ka | Wc | Vc | TW | P | Q | tmp | md | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Ti, CK.Hs, CK.Gc, CK.HG, CK.Ka, CK.Wc, CK.Vc, CK.TW, CK.P, CK.Q, CK.tmp,
      CK.md, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

/-- All stacks: the Bool output and the counters. -/
abbrev GK := SK CK

/-- Alphabets: Bool output, unit counters. -/
abbrev GΓ := SΓ CK


/-- Precomputation stages. -/
inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | dk | cp1 | cp2 | inc | v (s : MS) | dk2
  deriving DecidableEq, Fintype

/-- Stages of the routine emitting one literal. -/
inductive LS
  | cp1 | cp2 | ea | ma (s : MS) | da | eb | mb (s : MS) | db | ec
  | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- Labels, finite: situation numbers are `Fin N`, literal numbers `Fin m` (`m = nLits`). -/
inductive GL (N m : ℕ)
  | pre (s : PS)
  | tHead | tRest
  | tw (s : MS)
  | e00 (i : Fin N) | cv1 (i : Fin N) | cv2 (i : Fin N)
  | lit (i : Fin N) (j : Fin m) (s : LS)
  | fin (i : Fin N)
  | dtw | done
  deriving DecidableEq, Fintype

namespace GL

variable {N m : ℕ}

/-- Literal routine `j` of situation `i` (`done` if `j` is out of range; never used then). -/
def litL (i : Fin N) (j : ℕ) : GL N m := if h : j < m then .lit i ⟨j, h⟩ .cp1 else .done

/-- Where the routine goes after literal `j`: the previous literal, or the leading gap. -/
def after (i : Fin N) (j : ℕ) : GL N m := if j = 0 then .fin i else litL i (j - 1)

/-- Clause `i` (`dtw` if out of range). -/
def sitL (i : ℕ) : GL N m := if h : i < N then .e00 ⟨i, h⟩ else .dtw

/-- Where to go after situation `i`: the previous situation, or the end of the time step. -/
def afterS (i : ℕ) : GL N m := if i = 0 then .dtw else sitL (i - 1)

theorem litL_of_lt {i : Fin N} {j : ℕ} (h : j < m) : (litL i j : GL N m) = .lit i ⟨j, h⟩ .cp1 :=
  dite_eq_left h

theorem sitL_of_lt {i : ℕ} (h : i < N) : (sitL i : GL N m) = .e00 ⟨i, h⟩ := dite_eq_left h

end GL

section Machine

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N : ℕ)

/-- Literal `j`'s position is `t·W + kA j · (H·g) + kB j · W + cst i j`. -/
def kA (j : ℕ) : ℕ := if j = 0 then 0 else if j ≤ L.KK * L.d then (j - 1) / L.d else 0
/-- Row offset (in rows `W`) of literal `j`: `1` for the next-code literal, else `0`. -/
def kB (j : ℕ) : ℕ := if j = 0 then 0 else if j ≤ L.KK * L.d then 0 else 1
/-- Constant part of literal `j`'s position for situation `i`. -/
def cst (i j : ℕ) : ℕ :=
  if j = 0 then la i
  else if j ≤ L.KK * L.d then L.A + (j - 1) % L.d * L.g + wa i ((j - 1) / L.d) ((j - 1) % L.d)
  else na i
/-- Polarity of literal `j`: only the last (next-code) literal is positive. -/
def sgn (j : ℕ) : Bool := decide (j = L.nLits - 1)

/-- The routine for literal `j` of situation `i`: `Q := position`, emit the gap down from `P`,
the literal slot, drain `Q`. -/
def litP (i : Fin N) (j : Fin L.nLits) : LS → TM2.Stmt GΓ (GL N L.nLits) Bool
  | .cp1 => xfer (.c .TW) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit i j .cp1) (.lit i j .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.lit i j .cp2) (.lit i j .ea)
  | .ea => emitR (.c .Ka) (List.replicate (kA L j) ()) (.lit i j (.ma .head))
  | .ma s => mulS .Ka .md .HG .Q .tmp (fun s => .lit i j (.ma s)) (.lit i j .da) s
  | .da => xfer (.c .Ka) [] (.lit i j .da) (.lit i j .eb)
  | .eb => emitR (.c .Ka) (List.replicate (kB L j) ()) (.lit i j (.mb .head))
  | .mb s => mulS .Ka .md .Wc .Q .tmp (fun s => .lit i j (.mb s)) (.lit i j .db) s
  | .db => xfer (.c .Ka) [] (.lit i j .db) (.lit i j .ec)
  | .ec => emitR (.c .Q) (List.replicate (cst L la na wa i j) ()) (.lit i j .dec)
  | .dec => decr (.c .P) (.lit i j .bad) (.lit i j .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit i j .cmp)
      (.lit i j (.r .lt)) (.lit i j (.r .eq)) (.lit i j (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit i j (.r o)) (.lit i j (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit i j (.rB o))
      (if o = .eq then .lit i j .slot else .lit i j .emL)
  | .emL => emitR .out [false, true] (.lit i j .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (sgn L j))) (.lit i j .dq)
  | .dq => xfer (.c .Q) [] (.lit i j .dq) (GL.after i j)

/-- The generator. Input: `T` on `Tn`, `H` on `Hs`, everything else empty. -/
def prog : GL N L.nLits → TM2.Stmt GΓ (GL N L.nLits) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Ka) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Ka .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre .dk) s
  | .pre .dk => xfer (.c .Ka) [] (.pre .dk) (.pre .cp1)
  | .pre .cp1 => xfer (.c .Tn) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.pre .cp1) (.pre .cp2)
  | .pre .cp2 => xfer (.c .tmp) [⟨.c .Tn, ()⟩] (.pre .cp2) (.pre .inc)
  | .pre .inc => incr (.c .Ka) () (.pre (.v .head))
  | .pre (.v s) => mulS .Ka .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .dk2) s
  | .pre .dk2 => xfer (.c .Ka) [] (.pre .dk2) .tHead
  | .tHead => forHead (.c .Tn) (.c .Ti) () (.tw .head) .tRest
  | .tRest => xfer (.c .Ti) [⟨.c .Tn, ()⟩] .tRest .done
  | .tw s => mulS .Tn .md .Wc .TW .tmp .tw (GL.afterS N) s
  | .e00 i => emitR .out [false, false] (.cv1 i)
  | .cv1 i => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 i) (.cv2 i)
  | .cv2 i => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 i) (GL.litL i (L.nLits - 1))
  | .lit i j s => litP L la na wa N i j s
  | .fin i => xferE (.c .P) .out [false, true] (.fin i) (GL.afterS i)
  | .dtw => xfer (.c .TW) [] .dtw .tHead
  | .done => .halt

/-- **The generator as a genuine `FinTM2`** (finite stacks, labels, states; input stack `Tn`).
Only checks that the finiteness requirements are met; the run lemmas are about `prog`. -/
def genTM : FinTM2 where
  K := GK
  k₀ := .c .Tn
  k₁ := .out
  Γ := GΓ
  Λ := GL N L.nLits
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L la na wa N

end Machine

theorem kA_le (L : Layout) (j : ℕ) : kA L j ≤ L.KK := by
  unfold kA
  split_ifs with h0 h1
  · exact Nat.zero_le _
  · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; omega)
  · exact Nat.zero_le _

theorem kB_le (L : Layout) (j : ℕ) : kB L j ≤ 1 := by
  unfold kB; split_ifs <;> omega

/-! ## Correctness: one literal -/

section Correct

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N : ℕ)

/-- All scratch counters are empty. -/
structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  Ka : F .Ka = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

/-- One literal: from `P = q + gap + 1` (the previous boundary), compute `Q := q`, prepend the gap
and the literal slot, and leave `P = q`, all scratch counters empty again. -/
theorem lit_run (i : Fin N) (j : Fin L.nLits) (F : CK → ℕ) (hF : Rest F) (q gap : ℕ)
    (hq : q = F .TW + kA L j * F .HG + kB L j * F .Wc + cst L la na wa i j)
    (hp : F .P = q + gap + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L la na wa N)
      (gap * (3 * q + 6) + 2 * F .TW + L.KK * (2 * F .HG + 3) + 2 * L.KK + 2 * F .Wc + 4 * q + 22)
      ⟨some (.lit i j .cp1), v, st F o⟩
      ⟨some (GL.after i j), false,
        st (update F .P q) (encodeSlot (some (sgn L j)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, hKa, htmp, hmd, hc1, hc2⟩ := hF
  refine Bud.start ?_
  -- 1. Q := TW (copy through tmp)
  refine (copy_run (M := prog L la na wa N) (a := .c .TW) (c := .c .Q) (t := .c .tmp)
    (l₁ := .lit i j .cp1) (l₂ := .lit i j .cp2) (next := .lit i j .ea) rfl rfl
    (by decide) (by decide) (by decide) (F .TW) 0 v (st F o) rfl (by simp [hQ])
    (by simp [htmp])).bud ?_
  rw [update_st_c]
  -- 2. Ka := kA j
  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .ea)
    (next := .lit i j (.ma .head)) (k := .c .Ka) rfl _ _).bud ?_
  rw [emitR_st]
  -- 3. Q += Ka · HG
  refine (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .HG)
    (c := .c .Q) (t := .c .tmp) (head := .lit i j (.ma .head)) (body := .lit i j (.ma .body))
    (l₂ := .lit i j (.ma .l2)) (rest := .lit i j (.ma .rest)) (next := .lit i j .da)
    rfl rfl rfl rfl (by decide) _ _ _ _ _ rfl (by simp [hmd]) rfl rfl
    (by simp [htmp])).bud ?_
  rw [update_st_c]
  -- 4. drain Ka
  refine (xfer_run (M := prog L la na wa N) (self := .lit i j .da) (next := .lit i j .eb)
    (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
    rfl).bud ?_
  rw [addU_nil, update_st_nil]
  -- 5. Ka := kB j
  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .eb)
    (next := .lit i j (.mb .head)) (k := .c .Ka) rfl _ _).bud ?_
  rw [emitR_st]
  -- 6. Q += Ka · Wc
  refine (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .Wc)
    (c := .c .Q) (t := .c .tmp) (head := .lit i j (.mb .head)) (body := .lit i j (.mb .body))
    (l₂ := .lit i j (.mb .l2)) (rest := .lit i j (.mb .rest)) (next := .lit i j .db)
    rfl rfl rfl rfl (by decide) _ _ _ _ _ rfl (by simp [hmd]) rfl rfl
    (by simp [htmp])).bud ?_
  rw [update_st_c]
  -- 7. drain Ka
  refine (xfer_run (M := prog L la na wa N) (self := .lit i j .db) (next := .lit i j .ec)
    (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
    rfl).bud ?_
  rw [addU_nil, update_st_nil]
  -- 8. Q += cst
  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .ec)
    (next := .lit i j .dec) (k := .c .Q) rfl _ _).bud ?_
  rw [emitR_st]
  -- 9. gap emission: P goes from q + gap + 1 down to q
  refine (emitDiff_run (M := prog L la na wa N) (P := .c .P) (Q := .c .Q) (T1 := .c .c1)
    (T2 := .c .c2) (o := .out) (ys := [false, true]) (dec := .lit i j .dec)
    (cmpL := .lit i j .cmp) (emitL := .lit i j .emL) (ifZero := .lit i j .bad)
    (next := .lit i j .slot) (r := fun o => .lit i j (.r o)) (rB := fun o => .lit i j (.rB o))
    (out := fun o => if o = .eq then .lit i j .slot else .lit i j .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _ _
    (by simp [hp]) (by rw [st_c]; congr 1; simp [hKa, hq]; ring) (by simp [hc1])
    (by simp [hc2])).bud ?_
  rw [update_st_c, update_st_out]
  -- 10. the literal slot
  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .slot)
    (next := .lit i j .dq) (k := .out) rfl _ _).bud ?_
  rw [update_st_out]
  -- 11. drain Q
  refine (xfer_run (M := prog L la na wa N) (self := .lit i j .dq)
    (next := GL.after i j)
    (k := .c .Q) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
    rfl).bud ?_
  rw [addU_nil, update_st_nil]
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * F .HG + 3) (kA_le L j)
    have h2 := Nat.mul_le_mul_right (2 * F .Wc + 3) (kB_le L j)
    have h3 := kA_le L j
    have h4 := kB_le L j
    simp [hKa]
    omega
  simp only [TM2.Cfg.mk.injEq, true_and]
  refine ⟨rfl, ?_⟩
  congr 1
  funext x; cases x <;> simp [hQ, hKa]

end Correct

/-! ## Correctness: one clause -/

section Clause

variable {L : Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

theorem litPos_eq (H t i j : ℕ) :
    litPos L la na wa H t i j =
      t * L.rowW H + kA L j * (H * L.g) + kB L j * L.rowW H + cst L la na wa i j := by
  unfold litPos kA kB cst Layout.xIdx Layout.cIdx
  split_ifs <;> ring

theorem lits_drop (H t i j : ℕ) :
    (lits L la na wa H t i).drop j =
      (List.range' j (L.nLits - j)).map
        fun j => (litPos L la na wa H t i j, decide (j = L.nLits - 1)) := by
  rw [lits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

/-- The boundary before literal `j`: its position, or `V` past the last literal. -/
def bnd (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (T H t i j : ℕ) : ℕ :=
  if j < L.nLits then litPos L la na wa H t i j else L.numVars T H

theorem inc_drop {T H t i : ℕ} (ht : t < T) (hwf : WF L la na wa H i) (j : ℕ)
    (hjm : j ≤ L.nLits) :
    Inc (bnd L la na wa T H t i j) ((lits L la na wa H t i).drop j) (L.numVars T H) := by
  have h0 := lits_inc (T := T) ht hwf
  rw [lits_drop]
  unfold lits at h0
  refine inc_of_mono _ L.nLits _ (fun j hj => litPos_mono hwf j hj) (fun k hk => ?_)
    (L.nLits - j) j _ ?_ (fun hn => ?_) (fun hn => ?_)
  · -- the last literal is below `V`
    have := lits_inc (T := T) ht hwf
    have hlast : litPos L la na wa H t i k < L.numVars T H := by
      have hk' : k = L.KK * L.d + 1 := by unfold Layout.nLits at hk; omega
      simp only [hk', litPos, Nat.add_one_ne_zero, ite_false,
        ite_eq_right (show ¬(L.KK * L.d + 1 ≤ L.KK * L.d) by omega)]
      unfold Layout.xIdx Layout.numVars
      have h1 : na i < L.rowW H := lt_of_lt_of_le hwf.na_lt (Nat.le_add_right _ _)
      have h2 : (t + 1 + 1) * L.rowW H ≤ (T + 1) * L.rowW H := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_one_mul (t + 1)] at h2; omega
    exact hlast
  · omega
  · simp only [bnd]; split_ifs with h
    · omega
    · exact le_rfl
  · simp only [bnd, ite_eq_left (show j < L.nLits by omega)]; exact le_rfl

theorem bnd_lt {T H t i j : ℕ} (ht : t < T) (hwf : WF L la na wa H i) (hj : j < L.nLits) :
    litPos L la na wa H t i j < bnd L la na wa T H t i (j + 1) := by
  unfold bnd
  split_ifs with h
  · exact litPos_mono hwf j h
  · have := inc_drop (T := T) ht hwf j hj.le
    rw [lits_drop, show L.nLits - j = 0 + 1 by omega] at this
    simp only [List.range'_succ, List.map_cons, List.range'_zero, List.map_nil] at this
    obtain ⟨-, h2⟩ := this
    exact h2

/-- Resting counters inside the time loop at time `t`. -/
structure Base (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Rest F where
  TW : F .TW = t * L.rowW H
  HG : F .HG = H * L.g
  Wc : F .Wc = L.rowW H
  Vc : F .Vc = L.numVars T H

theorem Rest.update_P {F : CK → ℕ} (h : Rest F) (n : ℕ) : Rest (update F .P n) :=
  ⟨by simp [h.Q], by simp [h.Ka], by simp [h.tmp], by simp [h.md], by simp [h.c1], by simp [h.c2]⟩

/-- Time bound: per-literal cost apart from the gap loop. -/
def litE (L : Layout) (T H : ℕ) : ℕ :=
  6 * L.numVars T H + L.KK * (2 * (H * L.g) + 3) + 2 * L.KK + 2 * L.rowW H + 22

/-- Time bound: one whole clause. -/
def clauseB (L : Layout) (T H : ℕ) : ℕ :=
  L.numVars T H * (3 * L.numVars T H + 6) + L.nLits * litE L T H + 3 * L.numVars T H + 4

theorem bnd_le {T H t i : ℕ} (ht : t < T) (hwf : WF L la na wa H i) {j : ℕ} (hj : j ≤ L.nLits) :
    bnd L la na wa T H t i j ≤ L.numVars T H :=
  (inc_drop ht hwf j hj).le

theorem tW_le {T H t : ℕ} (ht : t < T) : t * L.rowW H ≤ L.numVars T H :=
  Nat.mul_le_mul_right _ (by omega)

/-- All literals of clause `(t, i)`, from the one before position `j` down to the first. -/
theorem lits_run {T H t : ℕ} {i : Fin N} (ht : t < T) (hwf : WF L la na wa H i) (F : CK → ℕ)
    (hF : Base L T H t F) (o : List Bool) :
    ∀ j, j ≤ L.nLits → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L la na wa N)
        (bnd L la na wa T H t i j * (3 * L.numVars T H + 6) + j * litE L T H)
        ⟨some (GL.after i j), v,
          st (update F .P (bnd L la na wa T H t i j))
            (gapEnc (bnd L la na wa T H t i j) ((lits L la na wa H t i).drop j)
              (L.numVars T H) ++ [false, false] ++ o)⟩
        ⟨some (.fin i), v',
          st (update F .P (bnd L la na wa T H t i 0))
            (gapEnc (bnd L la na wa T H t i 0) (lits L la na wa H t i)
              (L.numVars T H) ++ [false, false] ++ o)⟩ := by
  intro j
  induction j with
  | zero => intro _ v; exact ⟨v, by simpa [GL.after] using RunLe.refl _ _⟩
  | succ j ih =>
      intro hj v
      have hjm : j < L.nLits := by omega
      set p := litPos L la na wa H t i j with hp
      set b := bnd L la na wa T H t i (j + 1) with hb
      have hpb : p < b := bnd_lt ht hwf hjm
      have r := lit_run L la na wa N i ⟨j, hjm⟩ (update F .P b) (hF.toRest.update_P b) p (b - p - 1)
        (by rw [hp, litPos_eq]; simp [hF.TW, hF.HG, hF.Wc])
        (by simp; omega) (gapEnc b ((lits L la na wa H t i).drop (j + 1)) (L.numVars T H) ++
          [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GL.after, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel, GL.litL_of_lt hjm]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbj : bnd L la na wa T H t i j = p := by simp [bnd, hjm, hp]
      have hdrop : (lits L la na wa H t i).drop j =
          (p, sgn L j) :: (lits L la na wa H t i).drop (j + 1) := by
        rw [lits_drop, lits_drop, show L.nLits - j = (L.nLits - (j + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
        rfl
      have hshift := gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop ht hwf (j + 1) hj)
      rw [hbj, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      -- time: this literal's gap plus the rest fit in `b · (3V + 6)`
      have hbV := bnd_le ht hwf hj
      have htw := tW_le (L := L) (H := H) ht
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * L.numVars T H + 6 by omega)
      have h2 : (b - p - 1) * (3 * L.numVars T H + 6) + p * (3 * L.numVars T H + 6) ≤
          b * (3 * L.numVars T H + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF.TW, hF.HG, hF.Wc]
      rw [Nat.add_one_mul j]
      unfold litE
      omega

/-- One whole clause: from `e00 i` to the next situation (or the end of the time step). -/
theorem clause_run {T H t : ℕ} {i : Fin N} (ht : t < T) (hwf : WF L la na wa H i) (F : CK → ℕ)
    (hF : Base L T H t F) (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L la na wa N) (clauseB L T H) ⟨some (.e00 i), v, st F o⟩
      ⟨some (GL.afterS i), false,
        st F (encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i)) ++ o)⟩ := by
  -- terminator
  refine Bud.start ?_
  refine (emitR_run (M := prog L la na wa N) (self := .e00 i) (next := .cv1 i) (k := .out)
    rfl v _).bud ?_
  rw [update_st_out]
  -- P := V
  refine (copy_run (M := prog L la na wa N) (a := .c .Vc) (c := .c .P) (t := .c .tmp)
    (l₁ := .cv1 i) (l₂ := .cv2 i) (next := GL.litL i (L.nLits - 1)) rfl rfl
    (by decide) (by decide) (by decide) _ 0 v _ rfl (by simp [hP])
    (by simp [hF.tmp])).bud ?_
  rw [update_st_c]
  -- all literals
  have hm : L.nLits ≠ 0 := by unfold Layout.nLits; omega
  obtain ⟨v', r⟩ := lits_run (N := N) ht hwf F hF o L.nLits le_rfl
    (Flag.tag false)
  have hbm : bnd L la na wa T H t i L.nLits = L.numVars T H := by simp [bnd]
  rw [GL.after, ite_eq_right hm, hbm, List.drop_eq_nil_of_le (by simp [lits]), gapEnc, Nat.sub_self,
    rep_zero, List.nil_append] at r
  rw [hF.Vc, Nat.add_zero]
  refine r.bud ?_
  -- the leading gap
  refine (xferE_run (M := prog L la na wa N) (self := .fin i)
    (next := GL.afterS i) (k := .c .P) (o := .out)
    (ys := [false, true]) rfl (by simp) () _ v' _ rfl).bud ?_
  rw [update_st_nil, update_st_out]
  have e1 : update (update F .P (bnd L la na wa T H t i 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop (T := T) ht hwf 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i)) =
      rep [false, true] (bnd L la na wa T H t i 0) ++
        gapEnc (bnd L la na wa T H t i 0) (lits L la na wa H t i) (L.numVars T H) ++
          [false, false] := by
    rw [encodeClause_denseClause (lits_inc ht hwf), gapEnc_shift (Nat.zero_le _) h0,
      Nat.sub_zero]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le (j := 0) ht hwf (Nat.zero_le _)
  simp only [update_self]
  unfold clauseB
  omega

end Clause

/-! ## Correctness: situations, time steps, the whole generator -/

section Top

variable {L : Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

/-- Encoded clauses of time step `t`. -/
def blk (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N T H t : ℕ) : List Bool :=
  (List.range N).flatMap fun i => encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i))

theorem sits_run {T H t : ℕ} (ht : t < T) (hwf : ∀ i < N, WF L la na wa H i) (F : CK → ℕ)
    (hF : Base L T H t F) (hP : F .P = 0) :
    ∀ i, i < N → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L la na wa N) ((i + 1) * clauseB L T H) ⟨some (GL.sitL i), v, st F o⟩
        ⟨some .dtw, false, st F ((List.range (i + 1)).flatMap (fun i =>
          encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i))) ++ o)⟩ := by
  intro i
  induction i with
  | zero =>
      intro h0 o v
      rw [GL.sitL_of_lt h0]
      simpa [GL.afterS] using clause_run (i := ⟨0, h0⟩) ht (hwf 0 h0) F hF hP o v
  | succ i ih =>
      intro hi o v
      have r := clause_run (i := ⟨i + 1, hi⟩) ht (hwf (i + 1) hi) F hF hP o v
      rw [GL.sitL_of_lt hi]
      simp only [GL.afterS, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at r
      refine Bud.start (r.bud ?_)
      have := ih (by omega)
        (encodeClause (denseClause (L.numVars T H) (lits L la na wa H t (i + 1))) ++ o) false
      rw [List.range_succ (n := i + 1), List.flatMap_append, List.flatMap_singleton,
          List.append_assoc]
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (i + 1)]; omega

/-- Counter values at rest inside the time loop (all but `Tn`, `Ti`). -/
structure LoopP (L : Layout) (T H : ℕ) (f : CK → ℕ) : Prop extends Rest f where
  P : f .P = 0
  TW : f .TW = 0
  HG : f .HG = H * L.g
  Wc : f .Wc = L.rowW H
  Vc : f .Vc = L.numVars T H

/-- Time bound: one iteration of the time loop. -/
def bodyB (L : Layout) (N T H : ℕ) : ℕ :=
  T * (2 * L.rowW H + 3) + T * L.rowW H + T + 3 + N * clauseB L T H

/-- Time bound: the precomputation. -/
def preB (L : Layout) (T H : ℕ) : ℕ :=
  H * (2 * L.g + 3) + L.KK * (2 * (H * L.g) + 3) + (T + 1) * (2 * L.rowW H + 3) + H + 2 * L.KK +
    4 * T + 16

/-- Time bound: the whole generator (explicit; its polynomial form is `genBound_le`). -/
def genBound (L : Layout) (N T H : ℕ) : ℕ :=
  preB L T H + (T * (bodyB L N T H + 1) + T + 2)

/-- One iteration of the time loop, for time step `t`. -/
theorem time_body {T H t : ℕ} (ht : t < T) (hwf : ∀ i < N, WF L la na wa H i) (f : CK → ℕ)
    (hf : LoopP L T H f) (hTn : f .Tn = t) (o : List Bool) :
    RunLe (prog L la na wa N) (bodyB L N T H) ⟨some (.tw .head), Flag.tag true, st f o⟩
      ⟨some .tHead, Flag.tag false, st f (blk L la na wa N T H t ++ o)⟩ := by
  -- TW := t · W
  refine Bud.start ?_
  refine (mul_run (M := prog L la na wa N) (a := .c .Tn) (ad := .c .md) (b := .c .Wc)
    (c := .c .TW) (t := .c .tmp) (head := .tw .head) (body := .tw .body) (l₂ := .tw .l2)
    (rest := .tw .rest) (next := GL.afterS N) rfl rfl rfl rfl
    (by decide) _ _ _ _ _ rfl (by simp [hf.md]) rfl rfl
    (by simp [hf.tmp])).bud ?_
  rw [update_st_c]
  set F := update f .TW (f .Tn * f .Wc + f .TW) with hFdef
  have hB : Base L T H t F :=
    { Q := by simp [hFdef, hf.Q], Ka := by simp [hFdef, hf.Ka], tmp := by simp [hFdef, hf.tmp],
      md := by simp [hFdef, hf.md], c1 := by simp [hFdef, hf.c1], c2 := by simp [hFdef, hf.c2],
      TW := by simp [hFdef, hTn, hf.Wc, hf.TW], HG := by simp [hFdef, hf.HG],
      Wc := by simp [hFdef, hf.Wc], Vc := by simp [hFdef, hf.Vc] }
  have hFP : F .P = 0 := by simp [hFdef, hf.P]
  -- all situations
  have hs : RunLe (prog L la na wa N) (N * clauseB L T H)
      ⟨some (GL.afterS N), Flag.tag false, st F o⟩
      ⟨some .dtw, false, st F (blk L la na wa N T H t ++ o)⟩ := by
    by_cases hN : N = 0
    · subst hN
      simp only [GL.afterS, blk, List.range_zero, List.flatMap_nil, List.nil_append]
      exact RunLe.refl _ _
    · rw [GL.afterS, ite_eq_right hN]
      have := sits_run ht hwf F hB hFP (N - 1) (by omega) o (Flag.tag false)
      rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hN)] at this
  refine hs.bud ?_
  -- drain TW
  refine (xfer_run (M := prog L la na wa N) (self := .dtw) (next := .tHead) (k := .c .TW)
    (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _ rfl).bud ?_
  rw [addU_nil, update_st_nil]
  have : update F .TW 0 = f := by rw [hFdef, update_idem, ← hf.TW, update_eq_self]
  rw [this]
  refine Bud.fin ?_ rfl
  have h1 := Nat.mul_le_mul_right (2 * L.rowW H + 3) ht.le
  have h2 := Nat.mul_le_mul_right (L.rowW H) ht.le
  simp only [hFdef, update_self, hTn, hf.Wc, hf.TW]
  unfold bodyB
  omega

theorem ex_bud {α Λ : Type} {M : Λ → TM2.Stmt GΓ Λ Bool} {a K X : ℕ}
    {c d : TM2.Cfg GΓ Λ Bool} {P : α → Prop} {e : α → TM2.Cfg GΓ Λ Bool} (h : Run M a c d)
    (h' : ∃ x, P x ∧ Bud M (K + a) X d (e x)) : ∃ x, P x ∧ Bud M K X c (e x) := by
  obtain ⟨x, hx, h'⟩ := h'; exact ⟨x, hx, h.bud h'⟩

theorem LoopP.congr {T H : ℕ} {f f' : CK → ℕ} (h : LoopP L T H f)
    (e : ∀ x, x ≠ .Tn → x ≠ .Ti → f' x = f x) : LoopP L T H f' :=
  { Q := by rw [e _ (by decide) (by decide), h.Q], Ka := by rw [e _ (by decide) (by decide), h.Ka],
    tmp := by rw [e _ (by decide) (by decide), h.tmp],
    md := by rw [e _ (by decide) (by decide), h.md], c1 := by rw [e _ (by decide) (by decide),
        h.c1],
    c2 := by rw [e _ (by decide) (by decide), h.c2], P := by rw [e _ (by decide) (by decide), h.P],
    TW := by rw [e _ (by decide) (by decide), h.TW], HG := by rw [e _ (by decide) (by decide),
        h.HG],
    Wc := by rw [e _ (by decide) (by decide), h.Wc], Vc := by rw [e _ (by decide) (by decide),
        h.Vc] }

/-- Output after `ii` iterations of the time loop (time steps `T - ii, …, T - 1`). -/
def outAfter (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N T H ii : ℕ)
    (o : List Bool) : List Bool :=
  (List.range' (T - ii) ii).flatMap (blk L la na wa N T H) ++ o

/-- Initial counters: `T` on `Tn`, `H` on `Hs`. -/
def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

theorem encodeCNF_family (T H : ℕ) :
    encodeCNF (family L la na wa T H N) = (List.range T).flatMap (blk L la na wa N T H) := by
  simp [encodeCNF, family, List.flatMap_assoc, List.flatMap_map]; rfl

/-- **Correctness of the generator, with its explicit time bound**: started on `T`, `H` (in
unary) with empty scratch stacks, it halts at `done` within `genBound` steps, with exactly the
family's encoding prepended to the output stack. -/
theorem gen_run (T H : ℕ) (hwf : ∀ i < N, WF L la na wa H i) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      RunLe (prog L la na wa N) (genBound L N T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (family L la na wa T H N) ++ o := by
  -- precomputation
  have pre : ∃ f : CK → ℕ, (LoopP L T H f ∧ f .Tn = T ∧ f .Ti = 0) ∧
      Bud (prog L la na wa N) 0 (preB L T H) ⟨some (.pre .eg), false, st (initF T H) o⟩
        ⟨some .tHead, Flag.tag false, st f o⟩ := by
    refine ex_bud (emitR_run (M := prog L la na wa N) (self := .pre .eg)
      (next := .pre (.hg .head)) (k := .c .Gc) rfl _ _) ?_
    rw [emitR_st]
    refine ex_bud (mul_run (M := prog L la na wa N) (a := .c .Hs) (ad := .c .md) (b := .c .Gc)
      (c := .c .HG) (t := .c .tmp) (head := .pre (.hg .head)) (body := .pre (.hg .body))
      (l₂ := .pre (.hg .l2)) (rest := .pre (.hg .rest)) (next := .pre .ew) rfl rfl rfl rfl
      (by decide) _ _ _ _ _ rfl (by simp [initF]) rfl rfl (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (emitR_run (M := prog L la na wa N) (self := .pre .ew)
      (next := .pre .ek) (k := .c .Wc) rfl _ _) ?_
    rw [emitR_st]
    refine ex_bud (emitR_run (M := prog L la na wa N) (self := .pre .ek)
      (next := .pre (.w .head)) (k := .c .Ka) rfl _ _) ?_
    rw [emitR_st]
    refine ex_bud (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .HG)
      (c := .c .Wc) (t := .c .tmp) (head := .pre (.w .head)) (body := .pre (.w .body))
      (l₂ := .pre (.w .l2)) (rest := .pre (.w .rest)) (next := .pre .dk) rfl rfl rfl rfl
      (by decide) _ _ _ _ _ rfl (by simp [initF]) rfl rfl (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (xfer_run (M := prog L la na wa N) (self := .pre .dk) (next := .pre .cp1)
      (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
      rfl) ?_
    rw [addU_nil, update_st_nil]
    refine ex_bud (copy_run (M := prog L la na wa N) (a := .c .Tn) (c := .c .Ka) (t := .c .tmp)
      (l₁ := .pre .cp1) (l₂ := .pre .cp2) (next := .pre .inc) rfl rfl
      (by decide) (by decide) (by decide) _ 0 _ _ rfl (by simp) (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (incr_run_cnt (M := prog L la na wa N) (self := .pre .inc)
      (next := .pre (.v .head)) (k := .c .Ka) (u := ()) rfl _ (n := T + 0)
      (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .Wc)
      (c := .c .Vc) (t := .c .tmp) (head := .pre (.v .head)) (body := .pre (.v .body))
      (l₂ := .pre (.v .l2)) (rest := .pre (.v .rest)) (next := .pre .dk2) rfl rfl rfl rfl
      (by decide) _ _ _ _ _ rfl (by simp [initF]) rfl rfl
      (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (xfer_run (M := prog L la na wa N) (self := .pre .dk2) (next := .tHead)
      (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
      rfl) ?_
    rw [addU_nil, update_st_nil]
    refine ⟨_, ⟨?_, by simp [initF], by simp [initF]⟩, Bud.fin ?_ rfl⟩
    · exact
      { Q := (by simp [initF]), Ka := (by simp [initF]), tmp := (by simp [initF]),
        md := (by simp [initF]), c1 := (by simp [initF]), c2 := (by simp [initF]),
        P := (by simp [initF]), TW := (by simp [initF]), HG := (by simp [initF]),
        Wc := (by simp [initF, Layout.rowW]; ring),
        Vc := (by simp [initF, Layout.numVars, Layout.rowW]; ring) }
    · simp [initF, preB, Layout.rowW]
      ring_nf
      omega
  obtain ⟨f, ⟨hf, hTn, hTi⟩, hpre⟩ := pre
  -- the time loop
  obtain ⟨S', hloop, -, -, hout, -⟩ := forLoop_le (M := prog L la na wa N)
    (c := .c .Tn) (cd := .c .Ti) (uc := ()) (ucd := ()) (head := .tHead) (body := .tw .head)
    (rest := .tRest) (next := .done) rfl rfl (by decide) T (bodyB L N T H)
    (fun ii S => S .out = outAfter L la na wa N T H ii o ∧
      LoopP L T H (fun x => (S (.c x)).length))
    (fun ii S S' h ⟨h1, h2⟩ => ⟨by rw [h .out (by simp) (by simp), h1],
      h2.congr fun x h1 h2 => by rw [h (.c x) (by simpa using h1) (by simpa using h2)]⟩)
    (fun ii hii S hS1 hS2 ⟨h1, h2⟩ => by
      have hTn : (fun x => (S (.c x)).length) .Tn = T - 1 - ii := by simp [hS1]
      have r := time_body (N := N) (t := T - 1 - ii) (by omega) hwf _ h2 hTn (S .out)
      rw [← st_eta S] at r
      refine ⟨_, _, r, ?_, ?_, ?_, ?_⟩
      · exact (congrFun (st_eta S) (.c .Tn)).symm
      · exact (congrFun (st_eta S) (.c .Ti)).symm
      · simp only [st_out, h1, outAfter]
        rw [show T - (ii + 1) = T - 1 - ii by omega, List.range'_succ,
          show T - 1 - ii + 1 = T - ii by omega, List.flatMap_cons, List.append_assoc]
      · simpa using h2)
    (Flag.tag false) (st f o) (by simp [hTn]) (by simp [hTi])
    ⟨by simp [outAfter], by simpa using hf⟩
  exact ⟨_, S', (Bud.start hpre).trans hloop, by rw [hout, outAfter, Nat.sub_self,
    ← List.range_eq_range', encodeCNF_family]⟩

/-- Last session's statement (run existence only), now a corollary. -/
theorem gen_correct (T H : ℕ) (hwf : ∀ i < N, WF L la na wa H i) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      Reach (prog L la na wa N) ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (family L la na wa T H N) ++ o :=
  let ⟨v, S, h, h'⟩ := gen_run T H hwf o; ⟨v, S, h.reach, h'⟩

end Top

/-! ## The time bound is polynomial: `genBound ≤ genC · (T + H + 1)^5` -/

section Poly

/-- Layout with every constant equal to `k`. -/
def Layout.uni (k : ℕ) : Layout := ⟨k, k, k, k⟩

theorem genBound_mono {L L' : Layout} {N N' T T' H H' : ℕ} (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK)
    (hg : L.g ≤ L'.g) (hd : L.d ≤ L'.d) (hN : N ≤ N') (hT : T ≤ T') (hH : H ≤ H') :
    genBound L N T H ≤ genBound L' N' T' H' := by
  unfold genBound preB bodyB clauseB litE Layout.numVars Layout.rowW Layout.nLits
  gcongr

/-- With all constants `k ≥ 1` and `T = H = y ≥ 1`, every monomial is at most `k⁵ y⁵` and the
coefficients sum to 323 (the value at `k = y = 1`). -/
theorem genBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    genBound (Layout.uni k) k y y ≤ 323 * k ^ 5 * y ^ 5 := by
  have m : ∀ a b, a ≤ 5 → b ≤ 5 → k ^ a * y ^ b ≤ k ^ 5 * y ^ 5 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold genBound preB bodyB clauseB litE Layout.numVars Layout.rowW Layout.nLits Layout.uni
  simp only
  nlinarith [m 0 0 (by norm_num) (by norm_num), m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num), m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num), m 1 2 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num), m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num), m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num), m 3 3 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num), m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num), m 4 4 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num), m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num)]

/-- The constant of the time bound: depends on the layout and `N` only. -/
def genC (L : Layout) (N : ℕ) : ℕ := 323 * (L.A + L.KK + L.g + L.d + N + 1) ^ 5

theorem genBound_le (L : Layout) (N T H : ℕ) : genBound L N T H ≤ genC L N * (T + H + 1) ^ 5 := by
  have := genBound_mono (L := L) (L' := Layout.uni (L.A + L.KK + L.g + L.d + N + 1))
    (N := N) (N' := L.A + L.KK + L.g + L.d + N + 1) (T := T) (T' := T + H + 1) (H := H)
    (H' := T + H + 1) (by simp only [Layout.uni]; omega) (by simp only [Layout.uni]; omega)
    (by simp only [Layout.uni]; omega) (by simp only [Layout.uni]; omega) (by omega) (by omega)
    (by omega)
  exact this.trans (genBound_uni _ _ (by omega) (by omega))

open Polynomial in
/-- The bound as a `Polynomial ℕ` in `T + H` (the form `TM2ComputableInPolyTime` uses). -/
noncomputable def genPoly (L : Layout) (N : ℕ) : Polynomial ℕ := C (genC L N) * (X + 1) ^ 5

theorem genPoly_eval (L : Layout) (N T H : ℕ) :
    (genPoly L N).eval (T + H) = genC L N * (T + H + 1) ^ 5 := by
  simp [genPoly]

/-- **The time bound**: the generator emits the family within a polynomial number of steps. -/
theorem gen_time {L : Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N : ℕ} (T H : ℕ)
    (hwf : ∀ i < N, WF L la na wa H i) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      RunLe (prog L la na wa N) (genC L N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (family L la na wa T H N) ++ o :=
  let ⟨v, S, h, h'⟩ := gen_run T H hwf o; ⟨v, S, h.mono (genBound_le L N T H), h'⟩

end Poly

end Cslib.Complexity.CookLevin.Family
