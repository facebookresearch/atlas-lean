/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# Smith–Waterman local alignment: the `O(|xs| |ys|)` dynamic-programming table

Smith and Waterman (1981) compute the best local alignment score of two sequences by filling a
table `H` with `H[i][0] = H[0][j] = 0` and

`H[i+1][j+1] = max 0 (max (max (H[i][j] + σ x_i y_j) (H[i][j+1] + gap)) (H[i+1][j] + gap))`,

and returning the largest entry. Smith and Waterman allow a general weight for a gap of each
length; here, as in `SequenceAlignment`, gaps are linear (each gap column scores `gap`).

`CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment` defines the alignment score of
a pair of sequences (`nwScore`, the optimal global alignment score, with substitution score `σ`
and linear gap score `gap`), the cell `H[i][j]` as a specification
(`swCellScore` of the prefixes of lengths `i` and `j`), and proves that the largest cell
(`swScore`) is the optimal local alignment score, the largest global alignment score of a pair of
infixes (`localScore`), for `gap ≤ 0`. Those definitions are exponential-time specifications.
This file is the table itself, filled row by row, and proves that it computes them.

## Main results

* `nextRow_eq`: one row of the table is computed from the previous row in `O(|ys|)` operations.
* `swTab_eq_swScore`: **the table computes the Smith–Waterman score**, the largest cell.
* `swTab_eq_localScore`: **the table computes the optimal local alignment score** (`gap ≤ 0`):
  the maximum, over all pairs of infixes (contiguous substrings, possibly empty) of `xs` and `ys`,
  of their optimal global alignment score; it is at least `0`, the score of two empty infixes.

## Cost model

The cost is the number of additions and comparisons on `ℤ`. `nextRow` computes the `|ys| + 1`
cells of a row with `O(1)` operations each from the previous row (passed as an argument, so it
is computed once), and `swTab` computes `|xs| + 1` rows and their maxima: `O(|xs| |ys|)`
operations in total, with `O(|ys|)` live cells.

## References

* T. F. Smith and M. S. Waterman, *Identification of common molecular subsequences*,
  J. Mol. Biol. 147 (1981), 195–197.
* R. Durbin, S. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis*, Cambridge
  University Press, 1998, §2.3.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.SmithWaterman

open Cslib.Algorithms.Lean

variable {α : Type*} (σ : α → α → ℤ) (gap : ℤ)

/-- The cells `H[i+1][j+1], H[i+1][j+2], …` of a row from the remaining letters `b :: ys` of the
second sequence, the remaining cells `up :: prev` of the previous row, the previous row's cell
`diag` to the upper left and the cell `left` just computed. A previous row that is too short ends
the row early (this does not happen for rows of the table, `nextRow_eq`). -/
def nextRowAux (a : α) : List α → List ℤ → ℤ → ℤ → List ℤ
  | [], _, _, _ => []
  | _ :: _, [], _, _ => []
  | b :: ys, up :: prev, diag, left =>
      max 0 (max (max (diag + σ a b) (up + gap)) (left + gap)) ::
        nextRowAux a ys prev up (max 0 (max (max (diag + σ a b) (up + gap)) (left + gap)))

/-- The row of the table for the prefix extended by `a`, from the previous row: `H[i+1][0] = 0`,
then the recurrence left to right. -/
def nextRow (a : α) (ys : List α) (prev : List ℤ) : List ℤ :=
  0 :: nextRowAux σ gap a ys prev.tail (prev.headD 0) 0

/-- The Smith–Waterman table, filled row by row over the remaining letters of the first sequence:
`row` is the current row and `best` the largest cell of the earlier rows. -/
def swTabAux (ys : List α) : List α → List ℤ → ℤ → ℤ
  | [], row, best => max best (listMax row)
  | a :: xs, row, best => swTabAux ys xs (nextRow σ gap a ys row) (max best (listMax row))

/-- **The Smith–Waterman table**: the largest cell of the `(|xs| + 1) × (|ys| + 1)` table, with
the zero row `H[0][j] = 0` to start. -/
def swTab (xs ys : List α) : ℤ :=
  swTabAux σ gap ys xs (0 :: ys.map fun _ => 0) 0

private theorem le_listMax {xs : List ℤ} {a : ℤ} (ha : a ∈ xs) : a ≤ listMax xs := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
    rw [listMax, List.foldr_cons]
    rcases List.mem_cons.mp ha with h | h
    · rw [h]
      exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

private theorem listMax_le {xs : List ℤ} {y : ℤ} (h : ∀ a ∈ xs, a ≤ y) (hy : 0 ≤ y) :
    listMax xs ≤ y := by
  induction xs with
  | nil => exact hy
  | cons a as ih =>
    simp only [listMax, List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

private theorem nextRowAux_eq (a : α) (px : List α) :
    ∀ (rest pre : List α),
      nextRowAux σ gap a rest (rest.inits.tail.map fun q => swCellScore σ gap px (pre ++ q))
          (swCellScore σ gap px pre) (swCellScore σ gap (px ++ [a]) pre) =
        rest.inits.tail.map fun q => swCellScore σ gap (px ++ [a]) (pre ++ q)
  | [], _ => rfl
  | b :: r, pre => by
      have hc := swCellScore_eq σ gap px pre a b
      have ih := nextRowAux_eq a px r (pre ++ [b])
      have hi : r.inits = [] :: r.inits.tail := by cases r <;> simp
      rw [List.inits_cons, List.tail_cons, hi]
      simp only [List.map_cons, List.map_map, Function.comp_def, nextRowAux]
      rw [← hc]
      simpa [List.append_assoc, List.map_tail] using ih

/-- **One row of the table**: from the row of the prefix `px`, `nextRow` computes the row of
`px ++ [a]`: the cells `H[i+1][j] = swCellScore σ gap (px ++ [a]) py` for the prefixes `py` of
`ys`, shortest first. -/
theorem nextRow_eq (a : α) (px ys : List α) :
    nextRow σ gap a ys (ys.inits.map (swCellScore σ gap px)) =
      ys.inits.map (swCellScore σ gap (px ++ [a])) := by
  cases ys with
  | nil => simp [nextRow, nextRowAux, swCellScore_nil_right]
  | cons b ys =>
      have h := nextRowAux_eq σ gap a px (b :: ys) []
      simp only [List.nil_append, List.inits_cons, List.tail_cons, List.map_map,
        Function.comp_def, swCellScore_nil_right] at h
      simp only [nextRow, List.inits_cons, List.map_cons, List.tail_cons, List.headD_cons,
        List.map_map, Function.comp_def, swCellScore_nil_right]
      rw [h]

private theorem swTabAux_spec (ys : List α) :
    ∀ (rest pre : List α) (best : ℤ), 0 ≤ best →
      let R := swTabAux σ gap ys rest (ys.inits.map (swCellScore σ gap pre)) best
      best ≤ R ∧ (∀ q, q <+: rest → ∀ py, py <+: ys → swCellScore σ gap (pre ++ q) py ≤ R) ∧
        ∀ y, best ≤ y →
          (∀ q, q <+: rest → ∀ py, py <+: ys → swCellScore σ gap (pre ++ q) py ≤ y) → R ≤ y
  | [], pre, best, hb => by
      refine ⟨le_max_left _ _, fun q hq py hpy => ?_, fun y hy hall => ?_⟩
      · rw [List.prefix_nil.mp hq, List.append_nil]
        exact le_trans (le_listMax (List.mem_map.mpr ⟨py, (List.mem_inits _ _).mpr hpy, rfl⟩))
          (le_max_right _ _)
      · refine max_le hy (listMax_le (fun c hc => ?_) (le_trans hb hy))
        obtain ⟨py, hpy, rfl⟩ := List.mem_map.mp hc
        simpa using hall [] List.nil_prefix py ((List.mem_inits _ _).mp hpy)
  | a :: r, pre, best, hb => by
      intro R
      have hrow := nextRow_eq σ gap a pre ys
      obtain ⟨h1, h2, h3⟩ := swTabAux_spec ys r (pre ++ [a]) (max best
        (listMax (ys.inits.map (swCellScore σ gap pre)))) (le_trans hb (le_max_left _ _))
      have hR : R = swTabAux σ gap ys r (ys.inits.map (swCellScore σ gap (pre ++ [a])))
          (max best (listMax (ys.inits.map (swCellScore σ gap pre)))) := by
        simp only [R, swTabAux, hrow]
      rw [hR]
      refine ⟨le_trans (le_max_left _ _) h1, fun q hq py hpy => ?_, fun y hy hall => ?_⟩
      · rcases q with _ | ⟨c, q⟩
        · refine le_trans ?_ (le_trans (le_max_right _ _) h1)
          simpa using le_listMax (List.mem_map.mpr ⟨py, (List.mem_inits _ _).mpr hpy, rfl⟩)
        · obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.mp hq
          simpa [List.append_assoc] using h2 q hq' py hpy
      · refine h3 y (max_le hy (listMax_le (fun c hc => ?_) (le_trans hb hy))) ?_
        · obtain ⟨py, hpy, rfl⟩ := List.mem_map.mp hc
          simpa using hall [] List.nil_prefix py ((List.mem_inits _ _).mp hpy)
        · intro q hq py hpy
          simpa [List.append_assoc] using
            hall (a :: q) (List.cons_prefix_cons.mpr ⟨rfl, hq⟩) py hpy

/-- **The table computes the Smith–Waterman score**: `swTab` is the largest cell
`swCellScore σ gap px py` over all pairs of prefixes. -/
theorem swTab_eq_swScore (xs ys : List α) : swTab σ gap xs ys = swScore σ gap xs ys := by
  have hzero : (0 :: ys.map fun _ => (0 : ℤ)) = ys.inits.map (swCellScore σ gap []) := by
    rw [List.map_congr_left fun py _ => swCellScore_nil_left σ gap py]
    induction ys with
    | nil => rfl
    | cons b ys ih => simp [List.map_map, Function.comp_def, ← ih]
  obtain ⟨-, h2, h3⟩ := swTabAux_spec σ gap ys xs [] 0 le_rfl
  rw [swTab, hzero]
  refine le_antisymm (h3 _ ?_ fun q hq py hpy => ?_) (swScore_le σ gap fun p hp => ?_)
  · simpa [swCellScore_nil_left] using swCellScore_le_swScore σ gap (px := []) (py := [])
      (mem_prefixPairs.mpr ⟨List.nil_prefix, List.nil_prefix⟩)
  · exact swCellScore_le_swScore σ gap (mem_prefixPairs.mpr ⟨hq, hpy⟩)
  · rw [mem_prefixPairs] at hp
    simpa using h2 p.1 hp.1 p.2 hp.2

/-- **The table computes the optimal local alignment score** (Smith–Waterman 1981, `gap ≤ 0`):
`swTab` is the maximum, over all pairs of infixes of `xs` and `ys` (including the empty ones,
which give the floor `0`), of their optimal global alignment score `nwScore`. -/
theorem swTab_eq_localScore (hgap : gap ≤ 0) (xs ys : List α) :
    swTab σ gap xs ys = localScore σ gap xs ys := by
  rw [swTab_eq_swScore, localScore_eq_swScore σ gap hgap]

end Cslib.Bioinformatics.Alignment.SmithWaterman
