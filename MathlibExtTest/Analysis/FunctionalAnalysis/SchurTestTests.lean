/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.SchurTest

/-!
# Tests for Schur's test for finite matrices

Concrete checks on `ℂ²`:

* the identity matrix acts as the identity, with operator norm at most `1`;
* the all-ones matrix has operator norm at most `2`;
* the zero matrix has operator norm `0`;
* the diagonal matrix `diag (1, 2)` has operator norm at most `2`.
-/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.SchurTestTests

open MathlibExt.Analysis.FunctionalAnalysis.SchurTest

/-- Row and column sums of the identity matrix on `Fin 2` are `1`. -/
private theorem one_row_sum (i : Fin 2) :
    ∑ j : Fin 2, ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 := by
  fin_cases i <;> rw [Fin.sum_univ_two] <;> simp [Matrix.one_apply]

/-- Row and column sums of the identity matrix on `Fin 2` are `1`
(the column form). -/
private theorem one_col_sum (j : Fin 2) :
    ∑ i : Fin 2, ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 := by
  fin_cases j <;> rw [Fin.sum_univ_two] <;> simp [Matrix.one_apply]

/-- Row and column sums of the all-ones matrix on `Fin 2` are `2`. -/
private theorem allOnes_row_sum (i : Fin 2) :
    ∑ j : Fin 2, ‖(fun _ _ => (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 2 := by
  simp

/-- Row and column sums of the all-ones matrix on `Fin 2` are `2`
(the column form). -/
private theorem allOnes_col_sum (j : Fin 2) :
    ∑ i : Fin 2, ‖(fun _ _ => (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 2 := by
  simp

/-- Row sums of `diag (1, 2)` on `Fin 2` are at most `2`. -/
private theorem diag_row_sum (i : Fin 2) :
    ∑ j : Fin 2, ‖Matrix.diagonal (![1, 2] : Fin 2 → ℂ) i j‖ ≤ 2 := by
  fin_cases i <;> rw [Fin.sum_univ_two] <;> simp [Matrix.diagonal]

/-- Column sums of `diag (1, 2)` on `Fin 2` are at most `2`. -/
private theorem diag_col_sum (j : Fin 2) :
    ∑ i : Fin 2, ‖Matrix.diagonal (![1, 2] : Fin 2 → ℂ) i j‖ ≤ 2 := by
  fin_cases j <;> rw [Fin.sum_univ_two] <;> simp [Matrix.diagonal]

/-- The canonical identity matrix operator acts as the identity. -/
theorem schur_identity_apply (x : EuclideanSpace ℂ (Fin 2)) :
    (Matrix.toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap x = x := by
  simp [Matrix.toEuclideanLin]

/-- The operator norm of the identity matrix is at most `1`. -/
theorem schur_identity_norm_le :
    ‖(Matrix.toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap‖ ≤ 1 := by
  have h := norm_toEuclideanLin_le (1 : Matrix (Fin 2) (Fin 2) ℂ)
    zero_le_one zero_le_one one_row_sum one_col_sum
  simpa only [Real.sqrt_mul_self zero_le_one] using h

/-- The operator norm of the all-ones matrix on `ℂ²` is at most `2`. -/
theorem schur_allOnes_norm_le :
    ‖(Matrix.toEuclideanLin
      (fun _ _ => (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap‖ ≤ 2 := by
  have h := norm_toEuclideanLin_le
    (fun _ _ => (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    (by norm_num) (by norm_num) allOnes_row_sum allOnes_col_sum
  simpa only [Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)] using h

/-- The operator norm of the zero matrix is `0`. -/
theorem schur_zero_norm :
    ‖(Matrix.toEuclideanLin (0 : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap‖ = 0 := by
  simp

/-- The operator norm of `diag (1, 2)` on `ℂ²` is at most `2`. -/
theorem schur_diagonal_norm_le :
    ‖(Matrix.toEuclideanLin
      (Matrix.diagonal (![1, 2] : Fin 2 → ℂ))).toContinuousLinearMap‖ ≤ 2 := by
  have h := norm_toEuclideanLin_le (Matrix.diagonal (![1, 2] : Fin 2 → ℂ))
    (by norm_num) (by norm_num) diag_row_sum diag_col_sum
  simpa only [Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)] using h

/-! Canonical operator and scoped L2 importing clients. -/

open scoped Matrix.Norms.L2Operator

private def allOnesMatrix : Matrix (Fin 2) (Fin 2) ℂ := fun _ _ => 1

/-- The actual L2 norm of the all-ones matrix is at least 2, unlike its entrywise norm. -/
private theorem allOnes_l2_norm_ge : 2 ≤ ‖allOnesMatrix‖ := by
  let x : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hx : 0 < ‖x‖ := by
    apply norm_pos_iff.mpr
    intro h
    have h0 := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z 0) h
    norm_num [x] at h0
  have haction : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
      allOnesMatrix x = (2 : ℂ) • x := by
    change Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) allOnesMatrix
      (WithLp.toLp 2 (fun _ => (1 : ℂ))) =
        (2 : ℂ) • WithLp.toLp 2 (fun _ => (1 : ℂ))
    rw [Matrix.toEuclideanCLM_toLp]
    ext i
    simp [allOnesMatrix, Matrix.mulVec, dotProduct]
  have h := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) allOnesMatrix).le_opNorm x
  have hmul : 2 * ‖x‖ ≤ ‖allOnesMatrix‖ * ‖x‖ := by
    simpa [haction, norm_smul, Matrix.l2_opNorm_toEuclideanCLM] using h
  exact le_of_mul_le_mul_right hmul hx

/-- The rectangular all-ones 2×3 operator has the Schur bound √6. -/
theorem schur_rectangular_canonical_norm :
    ‖(Matrix.toEuclideanLin
      (fun _ _ => (1 : ℂ) : Matrix (Fin 2) (Fin 3) ℂ)).toContinuousLinearMap‖ ≤
      Real.sqrt 6 := by
  have h : ‖(Matrix.toEuclideanLin
      (fun _ _ => (1 : ℂ) : Matrix (Fin 2) (Fin 3) ℂ)).toContinuousLinearMap‖ ≤
      Real.sqrt (3 * 2) :=
    norm_toEuclideanLin_le _ (by norm_num) (by norm_num)
      (fun _ => by simp) (fun _ => by simp)
  simpa only [show (3 : ℝ) * 2 = 6 by norm_num] using h

/-- The square canonical identity operator has norm at most 1. -/
theorem schur_identity_canonical_clm_norm :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt (1 * 1) :=
  norm_toEuclideanCLM_le _ zero_le_one zero_le_one one_row_sum one_col_sum

/-- The scoped matrix L2 norm of the all-ones matrix is exactly 2. -/
theorem schur_allOnes_canonical_l2_norm : ‖allOnesMatrix‖ = 2 := by
  apply le_antisymm ?_ allOnes_l2_norm_ge
  have h : ‖allOnesMatrix‖ ≤ Real.sqrt (2 * 2) :=
    norm_matrix_l2_le allOnesMatrix (by norm_num) (by norm_num)
      allOnes_row_sum allOnes_col_sum
  simpa only [Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)] using h

/-- The rectangular bound accepts an empty domain without a nonempty premise. -/
theorem schur_empty_domain_canonical_bound (A : Matrix (Fin 2) (Fin 0) ℂ) :
    ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤ Real.sqrt (0 * 0) :=
  norm_toEuclideanLin_le A le_rfl le_rfl (fun _ => by simp) (fun j => Fin.elim0 j)

/-- The scoped matrix L2 bound also accepts an empty square index type. -/
theorem schur_empty_square_canonical_l2_bound (A : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖A‖ ≤ Real.sqrt (0 * 0) :=
  norm_matrix_l2_le A le_rfl le_rfl (fun i => Fin.elim0 i) (fun j => Fin.elim0 j)

end MathlibExtTest.Analysis.FunctionalAnalysis.SchurTestTests
