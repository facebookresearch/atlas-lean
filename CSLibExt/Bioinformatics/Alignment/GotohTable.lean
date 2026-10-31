/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.AffineAlignment

/-!
# Affine-gap alignment: the `O(|xs| |ys|)` three-layer Gotoh table

Gotoh (1982) computes the optimal alignment score under affine gap penalties (a run of `k ≥ 1`
gap columns costs `gapOpen + (k - 1) * gapExtend`) with three dynamic-programming matrices
instead of one, so that each cell costs `O(1)` and the whole table `O(|xs| |ys|)`. Flouri et
al. (2015) found errors in several published formulations and implementations of these
recurrences, which is why a table proved equal to an optimality specification is useful.

`CSLibExt.Algorithms.Lean.DynamicProgramming.AffineAlignment` defines, for a pair of sequences,
three exponential-time continuation values, one per state of the previous alignment column:
`gotohContNone` (a match, or no previous column), `gotohContGapX` (a gap in `ys`) and
`gotohContGapY` (a gap in `xs`), and proves that `gotohScore = gotohContNone` is the optimal
affine-gap score. This file tabulates the three values over all pairs of *suffixes* of `xs` and
`ys`: a cell holds the triple `(M, X, Y)` of the three continuation values (`cellSpec`), and the
first-column recurrences of `AffineAlignment` give each cell from three neighbours in `O(1)`.

The layers are indexed by the previous column's state and the table runs over suffixes (the
recurrences peel the first column), so this is Gotoh's three-matrix scheme applied to the
reversed sequences, not the prefix matrices `D, P, Q` of the original paper indexed by the last
column. The value returned is the same optimal score.

## Main results

* `firstRow_eq`, `nextRow_eq`: the row of the suffix `[]` and the row of `a :: xs` from the row
  of `xs`, each in `O(|ys|)` operations.
* `gotohRows_eq`: the row of `xs` holds `cellSpec xs t` for every suffix `t` of `ys`.
* `gotohTab_eq_gotohScore`: **the table computes the optimal affine-gap score**.
* `affineScore_le_gotohTab`, `exists_affineScore_eq_gotohTab`: every alignment scores at most
  `gotohTab`, and some alignment attains it.
* `gotohTab_eq_nwScore`: with `gapOpen = gapExtend = gap` the table computes the linear-gap
  Needleman–Wunsch score.

## Cost model

The cost is the number of additions and comparisons on `ℤ`. Each cell is three maxima of three
sums from three neighbouring cells (`step`), each computed once and shared through `let`;
`nextRow` computes `|ys| + 1` cells from the previous row, and `gotohRows` computes `|xs| + 1`
rows: `O(|xs| |ys|)` operations, with `O(|ys|)` live cells.

## References

* O. Gotoh, *An improved algorithm for matching biological sequences*, J. Mol. Biol. 162 (1982),
  705–708.
* T. Flouri, K. Kobert, T. Rognes and A. Stamatakis, *Are all global alignment algorithms and
  implementations correct?*, bioRxiv 031500 (2015).
* R. Durbin, S. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis*, Cambridge
  University Press, 1998, §2.4.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.Gotoh

open Cslib.Algorithms.Lean

variable {α : Type*} (σ : α → α → ℤ) (gapOpen gapExtend : ℤ)

/-- The specification of a cell: the three continuation values `(M, X, Y)` of the suffix pair
`(xs, ys)`, given that the previous column was a match, a gap in `ys`, or a gap in `xs`. -/
def cellSpec (xs ys : List α) : ℤ × ℤ × ℤ :=
  (gotohContNone σ gapOpen gapExtend xs ys, gotohContGapX σ gapOpen gapExtend xs ys,
    gotohContGapY σ gapOpen gapExtend xs ys)

/-- The cell of `(a :: xs, b :: ys)` from the cells `diag` of `(xs, ys)`, `up` of `(xs, b :: ys)`
and `left` of `(a :: xs, ys)`: a match continues from `M`, a gap in `ys` from `X` (extending if
the previous column was one), a gap in `xs` from `Y`. -/
def step (a b : α) (diag up left : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (max (diag.1 + σ a b) (max (up.2.1 + gapOpen) (left.2.2 + gapOpen)),
    max (diag.1 + σ a b) (max (up.2.1 + gapExtend) (left.2.2 + gapOpen)),
    max (diag.1 + σ a b) (max (up.2.1 + gapOpen) (left.2.2 + gapExtend)))

/-- The cell of `(a :: xs, [])` from the cell `o` of `(xs, [])`: one more gap column in `ys`. -/
def stepX (o : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (o.2.1 + gapOpen, o.2.1 + gapExtend, o.2.1 + gapOpen)

/-- The row of the suffix `[]` of `xs`: the cells of `([], t)` for the suffixes `t` of `ys`,
longest first, each one gap column in `xs` more than the next. -/
def firstRow : List α → List (ℤ × ℤ × ℤ)
  | [] => [0]
  | _ :: ys =>
      let rest := firstRow ys
      ((rest.headD 0).2.2 + gapOpen, (rest.headD 0).2.2 + gapOpen,
        (rest.headD 0).2.2 + gapExtend) :: rest

/-- The row of `a :: xs` from the row `prev` of `xs`, over the remaining suffixes of `ys`, longest
first; each cell uses the cell to its right in the same row. A row `prev` that is too short gives
junk cells (this does not happen for rows of the table, `nextRow_eq`). -/
def nextRow (a : α) : List α → List (ℤ × ℤ × ℤ) → List (ℤ × ℤ × ℤ)
  | [], prev => [stepX gapOpen gapExtend (prev.headD 0)]
  | b :: ys, prev =>
      let rest := nextRow a ys prev.tail
      step σ gapOpen gapExtend a b (prev.tail.headD 0) (prev.headD 0) (rest.headD 0) :: rest

/-- The row of the suffix `xs` (of the first sequence) of the table, computed from the rows of
its shorter suffixes. -/
def gotohRows (ys : List α) : List α → List (ℤ × ℤ × ℤ)
  | [] => firstRow gapOpen gapExtend ys
  | a :: xs => nextRow σ gapOpen gapExtend a ys (gotohRows ys xs)

/-- **The Gotoh table**: the `M` value of the cell `(xs, ys)`. -/
def gotohTab (xs ys : List α) : ℤ :=
  ((gotohRows σ gapOpen gapExtend ys xs).headD 0).1

private theorem headD_map_tails {β : Type*} (f : List α → β) (d : β) (ys : List α) :
    (ys.tails.map f).headD d = f ys := by
  cases ys <;> rfl

/-- **The first row**: `firstRow ys` holds the cells of `([], t)` for the suffixes `t` of `ys`. -/
theorem firstRow_eq (ys : List α) :
    firstRow gapOpen gapExtend ys = ys.tails.map (cellSpec σ gapOpen gapExtend []) := by
  induction ys with
  | nil =>
      simp [firstRow, cellSpec, gotohContNone_nil_left, gotohContGapX_nil_left,
        gotohContGapY_nil_left, gapRunCost]
      rfl
  | cons b ys ih =>
      rw [firstRow, ih, List.tails_cons, List.map_cons, headD_map_tails]
      congr 1
      simp only [cellSpec, gotohContNone_nil_left, gotohContGapX_nil_left,
        gotohContGapY_nil_left, List.length_cons]
      rw [← gapRunCost_succ gapOpen gapExtend .none .gapY,
        ← gapRunCost_succ gapOpen gapExtend .gapX .gapY,
        ← gapRunCost_succ gapOpen gapExtend .gapY .gapY]
      simp [gapCost, add_comm]

/-- **One row of the table**: from the row of the suffix `xs`, `nextRow` computes the row of
`a :: xs`: the cells `cellSpec (a :: xs) t` for the suffixes `t` of `ys`, longest first. -/
theorem nextRow_eq (a : α) (xs ys : List α) :
    nextRow σ gapOpen gapExtend a ys (ys.tails.map (cellSpec σ gapOpen gapExtend xs)) =
      ys.tails.map (cellSpec σ gapOpen gapExtend (a :: xs)) := by
  induction ys with
  | nil =>
      change nextRow σ gapOpen gapExtend a [] [cellSpec σ gapOpen gapExtend xs []] =
        [cellSpec σ gapOpen gapExtend (a :: xs) []]
      simp only [nextRow, List.headD_cons]
      congr 1
      simp only [stepX, cellSpec, gotohContNone_nil_right, gotohContGapX_nil_right,
        gotohContGapY_nil_right, List.length_cons]
      rw [← gapRunCost_succ gapOpen gapExtend .none .gapX,
        ← gapRunCost_succ gapOpen gapExtend .gapX .gapX,
        ← gapRunCost_succ gapOpen gapExtend .gapY .gapX]
      simp [gapCost, add_comm]
  | cons b ys ih =>
      rw [List.tails_cons, List.map_cons, List.map_cons, nextRow, List.tail_cons, ih,
        List.headD_cons, headD_map_tails, headD_map_tails]
      congr 1
      simp only [step, cellSpec]
      rw [gotohContNone_eq, gotohContGapX_eq, gotohContGapY_eq]

/-- **The rows of the table**: the row of `xs` holds `cellSpec xs t` for every suffix `t` of
`ys`, longest first. -/
theorem gotohRows_eq (xs ys : List α) :
    gotohRows σ gapOpen gapExtend ys xs = ys.tails.map (cellSpec σ gapOpen gapExtend xs) := by
  induction xs with
  | nil => exact firstRow_eq σ gapOpen gapExtend ys
  | cons a xs ih => rw [gotohRows, ih, nextRow_eq]

/-- **The table computes the optimal affine-gap score** (Gotoh 1982): `gotohTab = gotohScore`. -/
theorem gotohTab_eq_gotohScore (xs ys : List α) :
    gotohTab σ gapOpen gapExtend xs ys = gotohScore σ gapOpen gapExtend xs ys := by
  rw [gotohTab, gotohRows_eq, headD_map_tails]
  rfl

/-- **The table is an upper bound**: every alignment of `xs` and `ys` has affine-gap score at
most `gotohTab`. -/
theorem affineScore_le_gotohTab (A : Alignment α) (xs ys : List α) (hA : IsAlignment A xs ys) :
    affineScore σ gapOpen gapExtend A ≤ gotohTab σ gapOpen gapExtend xs ys := by
  rw [gotohTab_eq_gotohScore]
  exact affineScore_le_gotohScore σ gapOpen gapExtend A xs ys hA

/-- **The table is attained**: some alignment of `xs` and `ys` has affine-gap score `gotohTab`. -/
theorem exists_affineScore_eq_gotohTab (xs ys : List α) :
    ∃ A, IsAlignment A xs ys ∧
      affineScore σ gapOpen gapExtend A = gotohTab σ gapOpen gapExtend xs ys := by
  rw [gotohTab_eq_gotohScore]
  exact exists_affineScore_eq_gotohScore σ gapOpen gapExtend xs ys

/-- With `gapOpen = gapExtend = gap`, the Gotoh table computes the linear-gap Needleman–Wunsch
score. -/
theorem gotohTab_eq_nwScore (gap : ℤ) (hopen : gapOpen = gap) (hext : gapExtend = gap)
    (xs ys : List α) : gotohTab σ gapOpen gapExtend xs ys = nwScore σ gap xs ys := by
  rw [gotohTab_eq_gotohScore, gotohScore_eq_nwScore σ gapOpen gapExtend gap hopen hext]

end Cslib.Bioinformatics.Alignment.Gotoh
