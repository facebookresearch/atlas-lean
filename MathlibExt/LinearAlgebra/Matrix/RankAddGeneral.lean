/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Subadditivity of matrix rank over a field

For matrices `A B : Matrix m n K` over a field `K` with finitely many columns,
`rank (A + B) ≤ rank A + rank B`.

Source: R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press,
2013, §0.4.5 (rank inequalities: `rank (A + B) ≤ rank A + rank B`).

Mathlib has the cardinal-valued `LinearMap.rank_add_le` for linear maps but no statement about
`Matrix.rank`. The proof is the one already used for real `Fin a × Fin b` matrices in
`MathlibExt.Probability.Statistics.PCA` (private `rank_add_bound`, made public for that case
in T76) and in `MathlibExt.Biology.Omics.CovarianceBridge` (private `rank_add_le'`): the column
space of `A + B` lies in the sum of the column spaces. Here it is stated for arbitrary row and
column index types (only the columns need to be finite) and an arbitrary field.

## Main results

* `Matrix.rank_add_le` : `(A + B).rank ≤ A.rank + B.rank`.
* `Matrix.rank_neg` : `(-A).rank = A.rank`.
* `Matrix.rank_sub_le` : `(A - B).rank ≤ A.rank + B.rank`.
* `Matrix.rank_le_rank_add_rank_sub` : `A.rank ≤ B.rank + (A - B).rank`.
* `Matrix.rank_sum_le` : the rank of a finite sum is at most the sum of the ranks.
* `Matrix.rank_sum_le_card` : a sum of `s.card` matrices of rank at most one has rank at most
  `s.card` (the general form of PCA's private `rank_sum_bound`).
-/

public section

namespace Matrix

variable {m n K : Type*} [Fintype n] [Field K]

/-- **Subadditivity of matrix rank.** `rank (A + B) ≤ rank A + rank B` for matrices over a field
with finitely many columns (Horn–Johnson, *Matrix Analysis*, §0.4.5). -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Negation does not change the rank. -/
theorem rank_neg (A : Matrix m n K) : (-A).rank = A.rank := by
  have h : (-A).mulVecLin = -A.mulVecLin := by
    ext x i
    simp
  rw [Matrix.rank, Matrix.rank, h, LinearMap.range_neg]

/-- `rank (A - B) ≤ rank A + rank B`. -/
theorem rank_sub_le (A B : Matrix m n K) : (A - B).rank ≤ A.rank + B.rank := by
  rw [sub_eq_add_neg, ← rank_neg B]
  exact rank_add_le A (-B)

/-- Reverse triangle inequality for rank: `rank A ≤ rank B + rank (A - B)`. -/
theorem rank_le_rank_add_rank_sub (A B : Matrix m n K) : A.rank ≤ B.rank + (A - B).rank := by
  simpa using rank_add_le B (A - B)

/-- The rank of a finite sum of matrices is at most the sum of their ranks. -/
theorem rank_sum_le {ι : Type*} (s : Finset ι) (M : ι → Matrix m n K) :
    (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- A sum of matrices of rank at most one has rank at most the number of summands. -/
theorem rank_sum_le_card {ι : Type*} (s : Finset ι) (M : ι → Matrix m n K)
    (h : ∀ i ∈ s, (M i).rank ≤ 1) : (∑ i ∈ s, M i).rank ≤ s.card := by
  refine (rank_sum_le s M).trans ?_
  simpa using Finset.sum_le_sum h

end Matrix

end
