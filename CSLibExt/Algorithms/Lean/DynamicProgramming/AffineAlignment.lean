/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Affine-gap pairwise sequence alignment: the Gotoh algorithm

Pairwise alignment with affine gap penalties (Gotoh, *An improved algorithm for
matching biological sequences*, J. Mol. Biol. 1982; Durbin et al., *Biological
Sequence Analysis*, Cambridge, 1998): opening a gap run costs `gapOpen`, extending
an already-open run costs `gapExtend` per column, so a run of `k ≥ 1` gap columns
costs `gapOpen + (k - 1) * gapExtend`. Linear-gap Needleman–Wunsch is the special
case `gapOpen = gapExtend = gap`.

The alignment score is a fold over the alignment columns carrying the previous
column's gap state; the dynamic program is a single fuel recursion carrying the
same state. The three continuation values are specializations of that program:
`gotohContNone` (previous column a match), `gotohContGapX` (previous column
a gap in `ys`), `gotohContGapY` (previous column a gap in `xs`).

These are continuation values, not endpoint-restricted Gotoh matrices: each is
the best score of a suffix alignment *given* the previous column, and the first
column of the remaining suffix alignment is unrestricted (it may be a match or
either gap). The previous state only prices the next gap, via `gapCost`.

Main results:

* `affineScore_le_gotohScore`, `exists_affineScore_eq_gotohScore`: **Gotoh is
  optimal**: every valid alignment scores at most `gotohScore`, and some alignment
  attains it.
* `gotohContNone_eq`, `gotohContGapX_eq`, `gotohContGapY_eq`: **first-column
  recurrences** for the three continuation values.
* `gotohScore_eq_nwScore`: with `gapOpen = gapExtend = gap`,
  affine-gap alignment is linear-gap Needleman–Wunsch.

Cost model: as with `nwScore` / `swCellScore`, the DP is an exponential-time
*specification*, not a memoized table; a tabulated `O(|xs| * |ys|)` implementation
proved equal to it is future work.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-- The gap state carried by the affine-gap fold and DP: what the previous column was. -/
inductive GapState | none | gapX | gapY deriving DecidableEq, Repr

/-- The cost of a gap column continuing or opening a run. -/
def gapCost (gapOpen gapExtend : ℤ) (prev cur : GapState) : ℤ :=
  if prev = cur then gapExtend else gapOpen

section Affine

variable (σ : α → α → ℤ) (gapOpen gapExtend : ℤ)

/-- The affine-gap score of one alignment, by a fold carrying the previous gap state.
`gapX` is a `(some, none)` column (a gap in `ys`), `gapY` a `(none, some)` column.
The `(none, none)` column cannot occur in a valid alignment; it is scored as a no-op. -/
def affineScoreAux : Alignment α → GapState → ℤ
  | [], _ => 0
  | (some a, some b) :: A, _ => σ a b + affineScoreAux A .none
  | (some _, none) :: A, prev =>
      gapCost gapOpen gapExtend prev .gapX + affineScoreAux A .gapX
  | (none, some _) :: A, prev =>
      gapCost gapOpen gapExtend prev .gapY + affineScoreAux A .gapY
  | (none, none) :: A, _ => affineScoreAux A .none

/-- The affine-gap score of an alignment, starting with no open run. -/
def affineScore (A : Alignment α) : ℤ := affineScoreAux σ gapOpen gapExtend A .none

/-- The Gotoh DP, by fuel recursion on the total length, carrying the previous gap
state. The fuel is the sum of the two lengths. Implementation detail: use
`gotohContNone` / `gotohContGapX` / `gotohContGapY` / `gotohScore`, not this worker, which returns
`0` on insufficient fuel. -/
def gotohAux : ℕ → List α → List α → GapState → ℤ
  | 0, _, _, _ => 0
  | _ + 1, [], [], _ => 0
  | n + 1, [], b :: ys, prev => gapCost gapOpen gapExtend prev .gapY + gotohAux n [] ys .gapY
  | n + 1, a :: xs, [], prev => gapCost gapOpen gapExtend prev .gapX + gotohAux n xs [] .gapX
  | n + 1, a :: xs, b :: ys, prev =>
      max (σ a b + gotohAux n xs ys .none)
        (max (gapCost gapOpen gapExtend prev .gapX + gotohAux n xs (b :: ys) .gapX)
          (gapCost gapOpen gapExtend prev .gapY + gotohAux n (a :: xs) ys .gapY))

/-- Best score of a suffix alignment given the previous column was a match (or
there is no previous column, i.e. no open run). A continuation value, not an
endpoint-restricted matrix: the next column may be a match or either gap. -/
def gotohContNone (xs ys : List α) : ℤ :=
  gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys .none

/-- Best score of a suffix alignment given the previous column was a gap in `ys`
(an open `gapX` run). A continuation value, not an endpoint-restricted matrix:
the next column may be a match or either gap; the previous state only makes the
next gap in `ys` cost `gapExtend` instead of `gapOpen`. -/
def gotohContGapX (xs ys : List α) : ℤ :=
  gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys .gapX

/-- Best score of a suffix alignment given the previous column was a gap in `xs`
(an open `gapY` run). A continuation value, not an endpoint-restricted matrix:
the next column may be a match or either gap; the previous state only makes the
next gap in `xs` cost `gapExtend` instead of `gapOpen`. -/
def gotohContGapY (xs ys : List α) : ℤ :=
  gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys .gapY

/-- The optimal affine-gap alignment score: the `none` continuation (no previous
column, so no open run). -/
def gotohScore (xs ys : List α) : ℤ := gotohContNone σ gapOpen gapExtend xs ys

/-- Extra fuel does not change the DP. -/
private theorem gotohAux_succ_of_le : ∀ (m : ℕ) (xs ys : List α) (prev : GapState),
    xs.length + ys.length ≤ m →
    gotohAux σ gapOpen gapExtend m xs ys prev =
      gotohAux σ gapOpen gapExtend (m + 1) xs ys prev
  | 0, xs, ys, _, h => by
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      rfl
  | m + 1, [], [], _, _ => rfl
  | m + 1, [], b :: ys, _, _ => by
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [gotohAux]
      rw [gotohAux_succ_of_le m [] ys .gapY (by omega)]
  | m + 1, a :: xs, [], _, _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      simp only [gotohAux]
      rw [gotohAux_succ_of_le m xs [] .gapX (by omega)]
  | m + 1, a :: xs, b :: ys, prev, _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [gotohAux]
      rw [gotohAux_succ_of_le m xs ys .none (by omega),
        gotohAux_succ_of_le m xs (b :: ys) .gapX (by omega),
        gotohAux_succ_of_le m (a :: xs) ys .gapY (by omega)]

/-- The DP depends only on the lengths through the fuel bound. -/
private theorem gotohAux_eq_of_le (m : ℕ) (xs ys : List α) (prev : GapState)
    (h : xs.length + ys.length ≤ m) :
    gotohAux σ gapOpen gapExtend m xs ys prev =
      gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys prev := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [← ih, gotohAux_succ_of_le σ gapOpen gapExtend m xs ys prev hm]

/-- The cost of a gap run of length `k` in one direction, given the previous state:
continuing an open run costs `k * gapExtend`; otherwise a fresh run costs
`gapOpen + (k - 1) * gapExtend` (and `0` for `k = 0`). -/
def gapRunCost (gapOpen gapExtend : ℤ) (prev cur : GapState) (k : ℕ) : ℤ :=
  if prev = cur then (k : ℤ) * gapExtend
  else if k = 0 then 0 else gapOpen + ((k - 1 : ℕ) : ℤ) * gapExtend

/-- One more column extends a gap run: continuing costs `gapExtend`, opening costs `gapOpen`. -/
theorem gapRunCost_succ (gapOpen gapExtend : ℤ) (prev cur : GapState) (k : ℕ) :
    gapCost gapOpen gapExtend prev cur + gapRunCost gapOpen gapExtend cur cur k
      = gapRunCost gapOpen gapExtend prev cur (k + 1) := by
  by_cases hprev : prev = cur
  · subst hprev
    simp [gapCost, gapRunCost]
    ring
  · have hne : ¬ (k + 1 = 0) := by omega
    simp [gapCost, gapRunCost, hprev, hne]

/-- Aligning `[]` against `ys` is a single gap run in `ys`. -/
private theorem gotohAux_nil_left : ∀ (m : ℕ) (ys : List α) (prev : GapState),
    ys.length ≤ m →
    gotohAux σ gapOpen gapExtend m [] ys prev =
      gapRunCost gapOpen gapExtend prev .gapY ys.length := by
  intro m
  induction m with
  | zero =>
      intro ys prev hle
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hy
      simp [gotohAux, gapRunCost]
  | succ m ih =>
      intro ys prev hle
      cases ys with
      | nil => simp [gotohAux, gapRunCost]
      | cons b ys =>
          have hlen : (b :: ys).length = ys.length + 1 := rfl
          have hstep : gotohAux σ gapOpen gapExtend (m + 1) [] (b :: ys) prev =
              gapCost gapOpen gapExtend prev .gapY +
                gotohAux σ gapOpen gapExtend m [] ys .gapY := rfl
          rw [hstep, ih ys .gapY (by omega)]
          exact gapRunCost_succ gapOpen gapExtend prev .gapY ys.length

/-- Aligning `xs` against `[]` is a single gap run in `xs`. -/
private theorem gotohAux_nil_right : ∀ (m : ℕ) (xs : List α) (prev : GapState),
    xs.length ≤ m →
    gotohAux σ gapOpen gapExtend m xs [] prev =
      gapRunCost gapOpen gapExtend prev .gapX xs.length := by
  intro m
  induction m with
  | zero =>
      intro xs prev hle
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      simp [gotohAux, gapRunCost]
  | succ m ih =>
      intro xs prev hle
      cases xs with
      | nil => simp [gotohAux, gapRunCost]
      | cons a xs =>
          have hlen : (a :: xs).length = xs.length + 1 := rfl
          have hstep : gotohAux σ gapOpen gapExtend (m + 1) (a :: xs) [] prev =
              gapCost gapOpen gapExtend prev .gapX +
                gotohAux σ gapOpen gapExtend m xs [] .gapX := rfl
          rw [hstep, ih xs .gapX (by omega)]
          exact gapRunCost_succ gapOpen gapExtend prev .gapX xs.length

/-- Stripping a match column preserves validity. -/
theorem isAlignment_of_cons_match {a b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment ((some a, some b) :: A) (a :: xs) (b :: ys)) : IsAlignment A xs ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => h1 c (List.mem_cons_of_mem _ hc), ?_, ?_⟩
  · have h2' := h2
    rw [List.filterMap_cons] at h2'
    simpa using h2'
  · have h3' := h3
    rw [List.filterMap_cons] at h3'
    simpa using h3'

/-- Stripping a gap-in-`ys` column preserves validity. -/
theorem isAlignment_of_cons_gapX {a : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment ((some a, none) :: A) (a :: xs) ys) : IsAlignment A xs ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => h1 c (List.mem_cons_of_mem _ hc), ?_, ?_⟩
  · have h2' := h2
    rw [List.filterMap_cons] at h2'
    simpa using h2'
  · have h3' := h3
    rw [List.filterMap_cons] at h3'
    simpa using h3'

/-- Stripping a gap-in-`xs` column preserves validity. -/
theorem isAlignment_of_cons_gapY {b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment ((none, some b) :: A) xs (b :: ys)) : IsAlignment A xs ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => h1 c (List.mem_cons_of_mem _ hc), ?_, ?_⟩
  · have h2' := h2
    rw [List.filterMap_cons] at h2'
    simpa using h2'
  · have h3' := h3
    rw [List.filterMap_cons] at h3'
    simpa using h3'

/-- Prepending a match column preserves validity. -/
theorem isAlignment_cons_match {a b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment A xs ys) : IsAlignment ((some a, some b) :: A) (a :: xs) (b :: ys) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · exact h1 c hc
  · simp [List.filterMap_cons, h2]
  · simp [List.filterMap_cons, h3]

/-- Prepending a gap-in-`ys` column preserves validity. -/
theorem isAlignment_cons_gapX {a : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment A xs ys) : IsAlignment ((some a, none) :: A) (a :: xs) ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · exact h1 c hc
  · simp [List.filterMap_cons, h2]
  · simp [List.filterMap_cons, h3]

/-- Prepending a gap-in-`xs` column preserves validity. -/
theorem isAlignment_cons_gapY {b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment A xs ys) : IsAlignment ((none, some b) :: A) xs (b :: ys) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · exact h1 c hc
  · simp [List.filterMap_cons, h2]
  · simp [List.filterMap_cons, h3]

/-- One DP step on two nonempty sequences, in terms of the three continuation values. -/
private theorem gotohAux_cons_cons (a b : α) (xs ys : List α) (prev : GapState) :
    gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
        prev =
      max (σ a b + gotohContNone σ gapOpen gapExtend xs ys)
        (max (gapCost gapOpen gapExtend prev .gapX + gotohContGapX σ gapOpen gapExtend xs (b :: ys))
          (gapCost gapOpen gapExtend prev .gapY +
            gotohContGapY σ gapOpen gapExtend (a :: xs) ys)) := by
  have hfuel : (a :: xs).length + (b :: ys).length = (xs.length + ys.length + 1) + 1 := by
    simp only [List.length_cons]
    omega
  rw [hfuel]
  simp only [gotohAux]
  rw [← gotohAux_succ_of_le σ gapOpen gapExtend (xs.length + ys.length) xs ys .none le_rfl]
  have h3 : gotohAux σ gapOpen gapExtend (xs.length + ys.length + 1) (a :: xs) ys .gapY
      = gotohContGapY σ gapOpen gapExtend (a :: xs) ys := by
    rw [gotohAux_eq_of_le σ gapOpen gapExtend (xs.length + ys.length + 1) (a :: xs) ys .gapY
      (by simp only [List.length_cons]; omega)]
    rfl
  rw [h3]
  congr 1

/-- One DP step when the second sequence is empty. -/
private theorem gotohAux_cons_nil (a : α) (xs : List α) (prev : GapState) :
    gotohAux σ gapOpen gapExtend ((a :: xs).length + ([] : List α).length) (a :: xs)
        ([] : List α) prev =
      gapCost gapOpen gapExtend prev .gapX + gotohContGapX σ gapOpen gapExtend xs [] := by
  have hfuel : (a :: xs).length + ([] : List α).length = xs.length + 1 := by simp
  rw [hfuel]
  simp only [gotohAux]
  rfl

/-- One DP step when the first sequence is empty. -/
private theorem gotohAux_nil_cons (b : α) (ys : List α) (prev : GapState) :
    gotohAux σ gapOpen gapExtend (([] : List α).length + (b :: ys).length) ([] : List α)
        (b :: ys) prev =
      gapCost gapOpen gapExtend prev .gapY + gotohContGapY σ gapOpen gapExtend [] ys := by
  have hfuel : ([] : List α).length + (b :: ys).length = ys.length + 1 := by simp
  rw [hfuel]
  simp only [gotohAux]
  rw [show gotohContGapY σ gapOpen gapExtend [] ys
      = gotohAux σ gapOpen gapExtend (0 + ys.length) [] ys .gapY from rfl]
  rw [Nat.zero_add]

/-- **Gotoh is optimal** (general previous state): every valid alignment scores at
most the DP. -/
private theorem affineScoreAux_le_gotohAux : ∀ (A : Alignment α) (xs ys : List α) (prev : GapState),
    IsAlignment A xs ys →
    affineScoreAux σ gapOpen gapExtend A prev ≤
      gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys prev := by
  intro A
  induction A with
  | nil =>
      intro xs ys prev h
      obtain ⟨h1, h2, h3⟩ := h
      have hx : xs = [] := h2.symm
      have hy : ys = [] := h3.symm
      subst hx
      subst hy
      simp [affineScoreAux, gotohAux]
  | cons c A' ih =>
      intro xs ys prev h
      obtain ⟨c1, c2⟩ := c
      cases c1 with
      | none =>
          cases c2 with
          | none => exact absurd rfl (h.1 _ List.mem_cons_self)
          | some b =>
              -- Head column is `(none, some b)`: it consumes `b` from `ys` only.
              have hy : ys = b :: A'.filterMap Prod.snd := by
                simpa [List.filterMap_cons] using h.2.2.symm
              subst hy
              cases xs with
              | nil =>
                  have hA' := isAlignment_of_cons_gapY h
                  have hIH := ih _ _ .gapY hA'
                  rw [gotohAux_nil_cons]
                  show gapCost gapOpen gapExtend prev .gapY +
                      affineScoreAux σ gapOpen gapExtend A' .gapY ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapY))
                    le_rfl
              | cons a xs =>
                  have hA' := isAlignment_of_cons_gapY h
                  have hIH := ih _ _ .gapY hA'
                  rw [gotohAux_cons_cons]
                  show gapCost gapOpen gapExtend prev .gapY +
                      affineScoreAux σ gapOpen gapExtend A' .gapY ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapY))
                    (le_max_of_le_right (le_max_of_le_right le_rfl))
      | some a =>
          cases c2 with
          | none =>
              -- Head column is `(some a, none)`: it consumes `a` from `xs` only.
              have hx : xs = a :: A'.filterMap Prod.fst := by
                simpa [List.filterMap_cons] using h.2.1.symm
              subst hx
              cases ys with
              | nil =>
                  have hA' := isAlignment_of_cons_gapX h
                  have hIH := ih _ _ .gapX hA'
                  rw [gotohAux_cons_nil]
                  show gapCost gapOpen gapExtend prev .gapX +
                      affineScoreAux σ gapOpen gapExtend A' .gapX ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapX))
                    le_rfl
              | cons b ys =>
                  have hA' := isAlignment_of_cons_gapX h
                  have hIH := ih _ _ .gapX hA'
                  rw [gotohAux_cons_cons]
                  show gapCost gapOpen gapExtend prev .gapX +
                      affineScoreAux σ gapOpen gapExtend A' .gapX ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapX))
                    (le_max_of_le_right (le_max_of_le_left le_rfl))
          | some b =>
              have hx : xs = a :: A'.filterMap Prod.fst := by
                simpa [List.filterMap_cons] using h.2.1.symm
              have hy : ys = b :: A'.filterMap Prod.snd := by
                simpa [List.filterMap_cons] using h.2.2.symm
              subst hx
              subst hy
              have hA' := isAlignment_of_cons_match h
              have hIH := ih _ _ .none hA'
              rw [gotohAux_cons_cons]
              show σ a b + affineScoreAux σ gapOpen gapExtend A' .none ≤ _
              exact le_trans (add_le_add_right hIH (σ a b)) (le_max_of_le_left le_rfl)

/-- **Gotoh is attained**: some valid alignment achieves the DP. -/
private theorem exists_affineScore_eq_gotohAux : ∀ (n : ℕ) (xs ys : List α) (prev : GapState),
    xs.length + ys.length ≤ n →
    ∃ A, IsAlignment A xs ys ∧ affineScoreAux σ gapOpen gapExtend A prev =
      gotohAux σ gapOpen gapExtend n xs ys prev := by
  intro n
  induction n with
  | zero =>
      intro xs ys prev hle
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      exact ⟨[], ⟨by simp, rfl, rfl⟩, by simp [affineScoreAux, gotohAux]⟩
  | succ n ih =>
      intro xs ys prev hle
      cases xs with
      | nil =>
          cases ys with
          | nil =>
              exact ⟨[], ⟨by simp, rfl, rfl⟩, by simp [affineScoreAux, gotohAux]⟩
          | cons b ys =>
              obtain ⟨A', hA', hscore⟩ := ih [] ys .gapY
                (by have h1 : (b :: ys).length = ys.length + 1 := rfl; omega)
              refine ⟨(none, some b) :: A', isAlignment_cons_gapY hA', ?_⟩
              show gapCost gapOpen gapExtend prev .gapY +
                  affineScoreAux σ gapOpen gapExtend A' .gapY = _
              rw [hscore]
              simp only [gotohAux]
      | cons a xs =>
          cases ys with
          | nil =>
              obtain ⟨A', hA', hscore⟩ := ih xs [] .gapX
                (by have h1 : (a :: xs).length = xs.length + 1 := rfl; omega)
              refine ⟨(some a, none) :: A', isAlignment_cons_gapX hA', ?_⟩
              show gapCost gapOpen gapExtend prev .gapX +
                  affineScoreAux σ gapOpen gapExtend A' .gapX = _
              rw [hscore]
              simp only [gotohAux]
          | cons b ys =>
              have hlen1 : (a :: xs).length = xs.length + 1 := rfl
              have hlen2 : (b :: ys).length = ys.length + 1 := rfl
              obtain ⟨A1, hA1, hs1⟩ := ih xs ys .none (by omega)
              obtain ⟨A2, hA2, hs2⟩ := ih xs (b :: ys) .gapX (by omega)
              obtain ⟨A3, hA3, hs3⟩ := ih (a :: xs) ys .gapY (by omega)
              simp only [gotohAux]
              rcases le_total
                  (σ a b + gotohAux σ gapOpen gapExtend n xs ys .none)
                  (max (gapCost gapOpen gapExtend prev .gapX +
                    gotohAux σ gapOpen gapExtend n xs (b :: ys) .gapX)
                    (gapCost gapOpen gapExtend prev .gapY +
                      gotohAux σ gapOpen gapExtend n (a :: xs) ys .gapY)) with hmax | hmax
              · rw [max_eq_right hmax]
                rcases le_total
                    (gapCost gapOpen gapExtend prev .gapX +
                      gotohAux σ gapOpen gapExtend n xs (b :: ys) .gapX)
                    (gapCost gapOpen gapExtend prev .gapY +
                      gotohAux σ gapOpen gapExtend n (a :: xs) ys .gapY) with h2 | h2
                · rw [max_eq_right h2]
                  refine ⟨(none, some b) :: A3, isAlignment_cons_gapY hA3, ?_⟩
                  show gapCost gapOpen gapExtend prev .gapY +
                      affineScoreAux σ gapOpen gapExtend A3 .gapY = _
                  rw [hs3]
                · rw [max_eq_left h2]
                  refine ⟨(some a, none) :: A2, isAlignment_cons_gapX hA2, ?_⟩
                  show gapCost gapOpen gapExtend prev .gapX +
                      affineScoreAux σ gapOpen gapExtend A2 .gapX = _
                  rw [hs2]
              · rw [max_eq_left hmax]
                refine ⟨(some a, some b) :: A1, isAlignment_cons_match hA1, ?_⟩
                show σ a b + affineScoreAux σ gapOpen gapExtend A1 .none =
                  σ a b + gotohAux σ gapOpen gapExtend n xs ys .none
                rw [hs1]

/-- **Gotoh is optimal**: every valid alignment scores at most `gotohScore`. -/
theorem affineScore_le_gotohScore (A : Alignment α) (xs ys : List α)
    (hA : IsAlignment A xs ys) :
    affineScore σ gapOpen gapExtend A ≤ gotohScore σ gapOpen gapExtend xs ys :=
  affineScoreAux_le_gotohAux σ gapOpen gapExtend A xs ys .none hA

/-- **Gotoh is attained**: some valid alignment achieves `gotohScore`. -/
theorem exists_affineScore_eq_gotohScore (xs ys : List α) :
    ∃ A, IsAlignment A xs ys ∧
      affineScore σ gapOpen gapExtend A = gotohScore σ gapOpen gapExtend xs ys := by
  obtain ⟨A, hA, hscore⟩ := exists_affineScore_eq_gotohAux σ gapOpen gapExtend
    (xs.length + ys.length) xs ys .none le_rfl
  exact ⟨A, hA, hscore⟩

/-- **First-column recurrence for the `none` continuation.** -/
theorem gotohContNone_eq (a b : α) (xs ys : List α) :
    gotohContNone σ gapOpen gapExtend (a :: xs) (b :: ys) =
      max (gotohContNone σ gapOpen gapExtend xs ys + σ a b)
        (max (gotohContGapX σ gapOpen gapExtend xs (b :: ys) + gapOpen)
          (gotohContGapY σ gapOpen gapExtend (a :: xs) ys + gapOpen)) := by
  show gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
      .none = _
  rw [gotohAux_cons_cons]
  have hg1 : gapCost gapOpen gapExtend .none .gapX = gapOpen := by simp [gapCost]
  have hg2 : gapCost gapOpen gapExtend .none .gapY = gapOpen := by simp [gapCost]
  rw [hg1, hg2, add_comm (σ a b) (gotohContNone σ gapOpen gapExtend xs ys),
    add_comm gapOpen (gotohContGapX σ gapOpen gapExtend xs (b :: ys)),
    add_comm gapOpen (gotohContGapY σ gapOpen gapExtend (a :: xs) ys)]

/-- **First-column recurrence for the `gapX` continuation.** -/
theorem gotohContGapX_eq (a b : α) (xs ys : List α) :
    gotohContGapX σ gapOpen gapExtend (a :: xs) (b :: ys) =
      max (gotohContNone σ gapOpen gapExtend xs ys + σ a b)
        (max (gotohContGapX σ gapOpen gapExtend xs (b :: ys) + gapExtend)
          (gotohContGapY σ gapOpen gapExtend (a :: xs) ys + gapOpen)) := by
  show gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
      .gapX = _
  rw [gotohAux_cons_cons]
  have hg1 : gapCost gapOpen gapExtend .gapX .gapX = gapExtend := by simp [gapCost]
  have hg2 : gapCost gapOpen gapExtend .gapX .gapY = gapOpen := by simp [gapCost]
  rw [hg1, hg2, add_comm (σ a b) (gotohContNone σ gapOpen gapExtend xs ys),
    add_comm gapExtend (gotohContGapX σ gapOpen gapExtend xs (b :: ys)),
    add_comm gapOpen (gotohContGapY σ gapOpen gapExtend (a :: xs) ys)]

/-- **First-column recurrence for the `gapY` continuation.** -/
theorem gotohContGapY_eq (a b : α) (xs ys : List α) :
    gotohContGapY σ gapOpen gapExtend (a :: xs) (b :: ys) =
      max (gotohContNone σ gapOpen gapExtend xs ys + σ a b)
        (max (gotohContGapX σ gapOpen gapExtend xs (b :: ys) + gapOpen)
          (gotohContGapY σ gapOpen gapExtend (a :: xs) ys + gapExtend)) := by
  show gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
      .gapY = _
  rw [gotohAux_cons_cons]
  have hg1 : gapCost gapOpen gapExtend .gapY .gapX = gapOpen := by simp [gapCost]
  have hg2 : gapCost gapOpen gapExtend .gapY .gapY = gapExtend := by simp [gapCost]
  rw [hg1, hg2, add_comm (σ a b) (gotohContNone σ gapOpen gapExtend xs ys),
    add_comm gapOpen (gotohContGapX σ gapOpen gapExtend xs (b :: ys)),
    add_comm gapExtend (gotohContGapY σ gapOpen gapExtend (a :: xs) ys)]

/-- The `none` continuation against the empty sequence is a single gap run. -/
theorem gotohContNone_nil_left (ys : List α) :
    gotohContNone σ gapOpen gapExtend [] ys =
      gapRunCost gapOpen gapExtend .none .gapY ys.length :=
  gotohAux_nil_left σ gapOpen gapExtend (([] : List α).length + ys.length) ys .none (by simp)

/-- The `none` continuation against the empty sequence is a single gap run. -/
theorem gotohContNone_nil_right (xs : List α) :
    gotohContNone σ gapOpen gapExtend xs [] =
      gapRunCost gapOpen gapExtend .none .gapX xs.length :=
  gotohAux_nil_right σ gapOpen gapExtend (xs.length + ([] : List α).length) xs .none (by simp)

/-- The `gapX` continuation against the empty sequence is a single gap run. -/
theorem gotohContGapX_nil_left (ys : List α) :
    gotohContGapX σ gapOpen gapExtend [] ys =
      gapRunCost gapOpen gapExtend .gapX .gapY ys.length :=
  gotohAux_nil_left σ gapOpen gapExtend (([] : List α).length + ys.length) ys .gapX (by simp)

/-- The `gapX` continuation against the empty sequence is a single gap run. -/
theorem gotohContGapX_nil_right (xs : List α) :
    gotohContGapX σ gapOpen gapExtend xs [] =
      gapRunCost gapOpen gapExtend .gapX .gapX xs.length :=
  gotohAux_nil_right σ gapOpen gapExtend (xs.length + ([] : List α).length) xs .gapX (by simp)

/-- The `gapY` continuation against the empty sequence is a single gap run. -/
theorem gotohContGapY_nil_left (ys : List α) :
    gotohContGapY σ gapOpen gapExtend [] ys =
      gapRunCost gapOpen gapExtend .gapY .gapY ys.length :=
  gotohAux_nil_left σ gapOpen gapExtend (([] : List α).length + ys.length) ys .gapY (by simp)

/-- The `gapY` continuation against the empty sequence is a single gap run. -/
theorem gotohContGapY_nil_right (xs : List α) :
    gotohContGapY σ gapOpen gapExtend xs [] =
      gapRunCost gapOpen gapExtend .gapY .gapX xs.length :=
  gotohAux_nil_right σ gapOpen gapExtend (xs.length + ([] : List α).length) xs .gapY (by simp)

/-- With `gapOpen = gapExtend = gap`, the affine-gap score of an alignment is the
linear-gap score. -/
theorem affineScoreAux_eq_alignmentScore (gap : ℤ) (hopen : gapOpen = gap)
    (hext : gapExtend = gap) : ∀ (A : Alignment α) (prev : GapState),
    affineScoreAux σ gapOpen gapExtend A prev = alignmentScore σ gap A := by
  intro A
  induction A with
  | nil => intro prev; rfl
  | cons c A' ih =>
      intro prev
      have hg : ∀ cur : GapState, gapCost gapOpen gapExtend prev cur = gap := by
        intro cur
        by_cases h : prev = cur
        · subst h; simp [gapCost, hext]
        · simp [gapCost, h, hopen]
      obtain ⟨c1, c2⟩ := c
      cases c1 with
      | none =>
          cases c2 with
          | none =>
              show affineScoreAux σ gapOpen gapExtend A' .none =
                alignmentScore σ gap ((none, none) :: A')
              rw [ih .none]
              simp [alignmentScore, columnScore]
          | some b =>
              show gapCost gapOpen gapExtend prev .gapY +
                  affineScoreAux σ gapOpen gapExtend A' .gapY =
                alignmentScore σ gap ((none, some b) :: A')
              rw [ih .gapY, hg .gapY]
              simp [alignmentScore, columnScore]
      | some a =>
          cases c2 with
          | none =>
              show gapCost gapOpen gapExtend prev .gapX +
                  affineScoreAux σ gapOpen gapExtend A' .gapX =
                alignmentScore σ gap ((some a, none) :: A')
              rw [ih .gapX, hg .gapX]
              simp [alignmentScore, columnScore]
          | some b =>
              show σ a b + affineScoreAux σ gapOpen gapExtend A' .none =
                alignmentScore σ gap ((some a, some b) :: A')
              rw [ih .none]
              simp [alignmentScore, columnScore]

/-- With `gapOpen = gapExtend = gap`, the affine-gap score of an alignment is the
linear-gap score. -/
theorem affineScore_eq_alignmentScore (gap : ℤ) (hopen : gapOpen = gap)
    (hext : gapExtend = gap) (A : Alignment α) :
    affineScore σ gapOpen gapExtend A = alignmentScore σ gap A :=
  affineScoreAux_eq_alignmentScore σ gapOpen gapExtend gap hopen hext A .none

/-- With `gapOpen = gapExtend = gap`, affine-gap alignment is linear-gap
Needleman–Wunsch. -/
theorem gotohScore_eq_nwScore (gap : ℤ) (hopen : gapOpen = gap) (hext : gapExtend = gap)
    (xs ys : List α) :
    gotohScore σ gapOpen gapExtend xs ys = nwScore σ gap xs ys := by
  apply le_antisymm
  · obtain ⟨A, hA, hscore⟩ := exists_affineScore_eq_gotohScore σ gapOpen gapExtend xs ys
    rw [← hscore, affineScore_eq_alignmentScore σ gapOpen gapExtend gap hopen hext A]
    exact alignmentScore_le_nwScore σ gap xs ys A hA
  · obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
    rw [← hscore, ← affineScore_eq_alignmentScore σ gapOpen gapExtend gap hopen hext A]
    exact affineScore_le_gotohScore σ gapOpen gapExtend A xs ys hA

end Affine

end Cslib.Algorithms.Lean
