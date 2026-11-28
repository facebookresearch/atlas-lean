/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PosDef.DiagonalComparison

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the comparison of a positive definite form with its diagonal

* For the identity matrix, the coordinate bound reads `n i ^ 2 ≤ ∑ j, n j ^ 2`.
* For `A = !![2, 1; 1, 2]` over `ℚ`, the minor formula gives `A⁻¹ 0 0 = 2 / 3`.
* The real matrix `Y = !![2, 1; 1, 2]` is positive definite, with diagonal product `4` and
  determinant `3`, so the comparison holds with `μ = 4 / 3`:
  `2 * n i ^ 2 ≤ 4 / 3 * Q(n)` and `2 * n 0 ^ 2 + 2 * n 1 ^ 2 ≤ 2 * (4 / 3) * Q(n)`.
-/

@[expose] public section

open Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.PosDef.DiagonalComparison

/-- The coordinate bound for the identity matrix. -/
theorem sq_apply_le_one (n : Fin 3 → ℝ) (i : Fin 3) :
    n i ^ 2 ≤ (1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ i i * (n ⬝ᵥ (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n) :=
  PosDef.one.sq_apply_le_inv_apply_mul_dotProduct_mulVec i n

/-- The minor formula for `!![2, 1; 1, 2]` over `ℚ`: `A⁻¹ 0 0 = 2 / 3`. -/
theorem inv_two_one_one_two_zero_zero : (!![(2 : ℚ), 1; 1, 2])⁻¹ 0 0 = 2 / 3 := by
  rw [inv_apply_self_eq_det_submatrix_div_det, det_unique, det_fin_two]
  norm_num

/-- `!![2, 1; 1, 2]` is positive definite over `ℝ`: it is `1 + uᵀ * u` with `u = [1, 1]`. -/
theorem posDef_two_one_one_two : (!![(2 : ℝ), 1; 1, 2]).PosDef := by
  have h : (!![(2 : ℝ), 1; 1, 2]) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        conjTranspose (!![(1 : ℝ), 1] : Matrix (Fin 1) (Fin 2) ℝ) * !![(1 : ℝ), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num
  rw [h]
  exact PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self _)

/-- The diagonal product of `!![2, 1; 1, 2]` is at most `4 / 3` times its determinant. -/
theorem prod_diag_le_two_one_one_two :
    ∏ j, (!![(2 : ℝ), 1; 1, 2]) j j ≤ 4 / 3 * (!![(2 : ℝ), 1; 1, 2]).det := by
  rw [Fin.prod_univ_two, det_fin_two]
  norm_num

/-- The coordinate comparison for `!![2, 1; 1, 2]` with `μ = 4 / 3`. -/
theorem diag_mul_sq_le_two_one_one_two (i : Fin 2) (n : Fin 2 → ℝ) :
    (!![(2 : ℝ), 1; 1, 2]) i i * n i ^ 2 ≤ 4 / 3 * (n ⬝ᵥ (!![(2 : ℝ), 1; 1, 2]) *ᵥ n) :=
  posDef_two_one_one_two.diag_mul_sq_le_of_prod_diag_le prod_diag_le_two_one_one_two i n

/-- The summed comparison for `!![2, 1; 1, 2]` with `μ = 4 / 3`, written out. -/
theorem sum_diag_mul_sq_le_two_one_one_two (n : Fin 2 → ℝ) :
    2 * n 0 ^ 2 + 2 * n 1 ^ 2 ≤ 2 * (4 / 3) * (n ⬝ᵥ (!![(2 : ℝ), 1; 1, 2]) *ᵥ n) := by
  have h := posDef_two_one_one_two.sum_diag_mul_sq_le_of_prod_diag_le
    prod_diag_le_two_one_one_two n
  simpa [Fin.sum_univ_two] using h

end MathlibExtTest.LinearAlgebra.Matrix.PosDef.DiagonalComparison
