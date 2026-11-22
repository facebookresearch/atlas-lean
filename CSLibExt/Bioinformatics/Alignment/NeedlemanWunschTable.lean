/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# Needleman–Wunsch global alignment: the `O(|xs| |ys|)` dynamic-programming table

Needleman and Wunsch (1970) compute the optimal global alignment score of two sequences by
filling a table `F` with `F[i][0] = i * gap`, `F[0][j] = j * gap` and

`F[i+1][j+1] = max (max (F[i][j] + σ x_i y_j) (F[i][j+1] + gap)) (F[i+1][j] + gap)`,

and returning the last cell `F[|xs|][|ys|]` (linear gaps: each gap column scores `gap`).

`CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment` defines the optimal global
alignment score `nwScore` as an exponential-time specification and proves it optimal
(`alignmentScore_le_nwScore`, `exists_alignmentScore_eq_nwScore`). This file is the table, filled
row by row, and proves that it computes `nwScore`, for every `σ` and every `gap`.

## Main results

* `nextRow_eq`: one row of the table is computed from the previous row in `O(|ys|)` operations.
* `nwRows_eq`: the last row of the table is `F[|xs|][j] = nwScore xs (ys.take j)`.
* `nwTab_eq_nwScore`: **the table computes the optimal global alignment score**.

## Cost model

The cost is the number of additions and comparisons on `ℤ`. `nextRow` computes the `|ys| + 1`
cells of a row with `O(1)` operations each from the previous row (passed as an argument, so it is
computed once), and `nwRows` computes `|xs| + 1` rows: `O(|xs| |ys|)` operations, with `O(|ys|)`
live cells.

## References

* S. B. Needleman and C. D. Wunsch, *A general method applicable to the search for similarities
  in the amino acid sequence of two proteins*, J. Mol. Biol. 48 (1970), 443–453.
* R. Durbin, S. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis*, Cambridge
  University Press, 1998, §2.3.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.NeedlemanWunsch

open Cslib.Algorithms.Lean

variable {α : Type*} (σ : α → α → ℤ) (gap : ℤ)

/-- The cells `F[i+1][j+1], F[i+1][j+2], …` of a row from the remaining letters `b :: ys` of the
second sequence, the remaining cells `up :: prev` of the previous row, the previous row's cell
`diag` to the upper left and the cell `left` just computed. A previous row that is too short ends
the row early (this does not happen for rows of the table, `nextRow_eq`). -/
def nextRowAux (a : α) : List α → List ℤ → ℤ → ℤ → List ℤ
  | [], _, _, _ => []
  | _ :: _, [], _, _ => []
  | b :: ys, up :: prev, diag, left =>
      max (max (diag + σ a b) (up + gap)) (left + gap) ::
        nextRowAux a ys prev up (max (max (diag + σ a b) (up + gap)) (left + gap))

/-- The row of the table for the prefix extended by `a`, from the previous row: the first cell is
one more gap than the previous row's first cell, then the recurrence left to right. -/
def nextRow (a : α) (ys : List α) (prev : List ℤ) : List ℤ :=
  (prev.headD 0 + gap) :: nextRowAux σ gap a ys prev.tail (prev.headD 0) (prev.headD 0 + gap)

/-- The rows of the table, filled top to bottom over the letters of the first sequence; the
result is the last row. Row `0` is `F[0][j] = j * gap`. -/
def nwRowsAux (ys : List α) : List α → List ℤ → List ℤ
  | [], row => row
  | a :: xs, row => nwRowsAux ys xs (nextRow σ gap a ys row)

/-- The last row `F[|xs|][·]` of the Needleman–Wunsch table. -/
def nwRows (xs ys : List α) : List ℤ :=
  nwRowsAux σ gap ys xs ((List.range (ys.length + 1)).map fun j : ℕ => gap * (j : ℤ))

/-- **The Needleman–Wunsch table**: its last cell `F[|xs|][|ys|]`. -/
def nwTab (xs ys : List α) : ℤ :=
  (nwRows σ gap xs ys).getLastD 0

private theorem nextRowAux_eq (a : α) (px : List α) :
    ∀ (rest pre : List α),
      nextRowAux σ gap a rest (rest.inits.tail.map fun q => nwScore σ gap px (pre ++ q))
          (nwScore σ gap px pre) (nwScore σ gap (px ++ [a]) pre) =
        rest.inits.tail.map fun q => nwScore σ gap (px ++ [a]) (pre ++ q)
  | [], _ => rfl
  | b :: r, pre => by
      have hc := nwScore_snoc σ gap px pre a b
      have ih := nextRowAux_eq a px r (pre ++ [b])
      have hi : r.inits = [] :: r.inits.tail := by cases r <;> simp
      rw [List.inits_cons, List.tail_cons, hi]
      simp only [List.map_cons, List.map_map, Function.comp_def, nextRowAux]
      rw [← hc]
      simpa [List.append_assoc, List.map_tail] using ih

private theorem nwScore_snoc_nil (px : List α) (a : α) :
    nwScore σ gap (px ++ [a]) [] = nwScore σ gap px [] + gap := by
  rw [nwScore_nil_right, nwScore_nil_right]
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  ring

/-- **One row of the table**: from the row of the prefix `px`, `nextRow` computes the row of
`px ++ [a]`: the cells `nwScore (px ++ [a]) py` for the prefixes `py` of `ys`, shortest first. -/
theorem nextRow_eq (a : α) (px ys : List α) :
    nextRow σ gap a ys (ys.inits.map (nwScore σ gap px)) =
      ys.inits.map (nwScore σ gap (px ++ [a])) := by
  cases ys with
  | nil => simp [nextRow, nextRowAux, nwScore_snoc_nil]
  | cons b ys =>
      have h := nextRowAux_eq σ gap a px (b :: ys) []
      simp only [List.nil_append, List.inits_cons, List.tail_cons, List.map_map,
        Function.comp_def, nwScore_snoc_nil] at h
      simp only [nextRow, List.inits_cons, List.map_cons, List.tail_cons, List.headD_cons,
        List.map_map, Function.comp_def, nwScore_snoc_nil]
      rw [h]

private theorem nwRowsAux_eq (ys : List α) :
    ∀ (rest pre : List α),
      nwRowsAux σ gap ys rest (ys.inits.map (nwScore σ gap pre)) =
        ys.inits.map (nwScore σ gap (pre ++ rest))
  | [], pre => by simp [nwRowsAux]
  | a :: r, pre => by
      rw [nwRowsAux, nextRow_eq, nwRowsAux_eq ys r (pre ++ [a])]
      simp [List.append_assoc]

private theorem firstRow_eq (ys : List α) :
    (List.range (ys.length + 1)).map (fun j : ℕ => gap * (j : ℤ)) =
      ys.inits.map (nwScore σ gap []) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j ≤ ys.length := by simp at h1; omega
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_inits,
      nwScore_nil_left, List.length_take, Nat.min_eq_left hj]

/-- **The last row of the table** is `F[|xs|][j] = nwScore xs (ys.take j)`: the cells
`nwScore xs py` over the prefixes `py` of `ys`, shortest first. -/
theorem nwRows_eq (xs ys : List α) :
    nwRows σ gap xs ys = ys.inits.map (nwScore σ gap xs) := by
  rw [nwRows, firstRow_eq, nwRowsAux_eq, List.nil_append]

/-- **The table computes the optimal global alignment score** (Needleman–Wunsch 1970), for every
substitution score `σ` and gap score `gap`. -/
theorem nwTab_eq_nwScore (xs ys : List α) : nwTab σ gap xs ys = nwScore σ gap xs ys := by
  rw [nwTab, nwRows_eq]
  have hl : ys.inits.length - 1 = ys.length := by simp
  rw [List.getLastD_eq_getLast?, List.getLast?_map, List.getLast?_eq_getElem?, hl,
    List.getElem?_eq_getElem (by simp), List.getElem_inits, List.take_length]
  rfl

end Cslib.Bioinformatics.Alignment.NeedlemanWunsch
