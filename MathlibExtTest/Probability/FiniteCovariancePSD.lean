/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteCovariancePSD

/-!
# Tests for positive semidefiniteness of finite covariance matrices

Two equally likely states with perfectly correlated returns `(1, 2)` and `(-1, -2)`: the covariance
matrix is `!![1, 2; 2, 4]`, the portfolio `(2, -1)` has zero variance (computed directly and through
`dotProduct_covMatrix_mulVec`), the portfolio `(1, 0)` has variance `1`, and the matrix is positive
semidefinite but singular.
-/

@[expose] public section

open Matrix

namespace MathlibExtTest.Probability.FiniteCovariancePSD

open _root_.MathlibExt.Probability.FiniteProbability

theorem test_covMatrix :
    covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![-1, -2]] = !![1, 2; 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covMatrix_apply, covariance, expectation, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply] <;>
    norm_num

theorem test_quadform :
    ![2, -1] ⬝ᵥ (covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![-1, -2]] *ᵥ ![2, -1]) = 0 := by
  rw [test_covMatrix, Matrix.dot_mulVec_eq_sum_sum]
  norm_num [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]

theorem test_posSemidef :
    (covMatrix ![1 / 2, 1 / 2] ![![1, 2], ![-1, -2]]).PosSemidef :=
  covMatrix_posSemidef
    (fun x => by fin_cases x <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]) _

theorem test_variance_zero :
    variance ![1 / 2, 1 / 2]
      (fun x => (![2, -1] : Fin 2 → ℝ) ⬝ᵥ ![![1, 2], ![-1, -2]] x) = 0 := by
  have h := dotProduct_covMatrix_mulVec ![1 / 2, 1 / 2] ![![1, 2], ![-1, -2]]
    (![2, -1] : Fin 2 → ℝ)
  rw [← h]
  exact test_quadform

theorem test_variance_one :
    variance ![1 / 2, 1 / 2]
      (fun x => (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![![1, 2], ![-1, -2]] x) = 1 := by
  have h := dotProduct_covMatrix_mulVec ![1 / 2, 1 / 2] ![![1, 2], ![-1, -2]]
    (![1, 0] : Fin 2 → ℝ)
  rw [← h, test_covMatrix, Matrix.dot_mulVec_eq_sum_sum]
  norm_num [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]

end MathlibExtTest.Probability.FiniteCovariancePSD
