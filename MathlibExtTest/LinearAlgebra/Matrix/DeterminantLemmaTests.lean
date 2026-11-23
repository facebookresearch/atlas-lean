/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.DeterminantLemma

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the matrix determinant lemma

With `A = !![2, 1; 0, 3]`, `u = ![1, 2]`, `v = ![3, -1]` the update is
`!![5, 0; 6, 1]` of determinant `5`, while `det A = 6` and the adjugate
correction is `v ⬝ᵥ (adjugate A *ᵥ u) = -1`. The second test has singular
`A = !![1, 2; 2, 4]` (so Mathlib's invertible version does not apply) and the
update `!![1, 3; 2, 4]` of determinant `-2`, equal to the adjugate correction.
-/

namespace MathlibExtTest.DeterminantLemma

open Matrix

/-- The matrix determinant lemma on an invertible `2 × 2` matrix. -/
example : ((!![2, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ) +
    vecMulVec ![1, 2] ![3, -1]).det = 5 := by
  rw [det_add_vecMulVec]
  decide

/-- The matrix determinant lemma on a singular `2 × 2` matrix: `det A = 0`
and the whole determinant comes from the adjugate correction. -/
example : ((!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℤ) +
    vecMulVec ![1, 0] ![0, 1]).det = -2 := by
  rw [det_add_vecMulVec]
  decide

/-- The `replicateCol` / `replicateRow` form, as stated in Mathlib's TODO. -/
example : ((!![2, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ) +
    replicateCol Unit (![1, 2] : Fin 2 → ℤ) *
      replicateRow Unit (![3, -1] : Fin 2 → ℤ)).det = 5 := by
  rw [det_add_replicateCol_mul_replicateRow_general]
  decide

/-- A rank-one update of a singular matrix can be a unit: here the update has
determinant `-2 ≠ 0` over `ℚ`. -/
example : IsUnit ((!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ) +
    vecMulVec ![1, 0] ![0, 1]) := by
  rw [isUnit_add_vecMulVec_iff]
  have h : (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ).det +
      ![0, 1] ⬝ᵥ (adjugate !![1, 2; 2, 4] *ᵥ ![1, 0]) = -2 := by
    (simp [Matrix.det_fin_two, Matrix.adjugate_fin_two, dotProduct,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]; norm_num)
  rw [h]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- The general version agrees with Mathlib's invertible version on an
invertible matrix. -/
example : ((!![2, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ) +
    vecMulVec ![1, 2] ![3, -1]).det = 5 := by
  have hinv : (!![2, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ =
      !![1 / 2, -(1 / 6); 0, 1 / 3] := by
    rw [Matrix.inv_def]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.det_fin_two, Matrix.adjugate_fin_two] <;> norm_num
  rw [det_add_vecMulVec_of_isUnit_det (!![2, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ)
    ![1, 2] ![3, -1] (by
      rw [isUnit_iff_ne_zero]
      norm_num [Matrix.det_fin_two]), hinv]
  simp [Matrix.det_fin_two, dotProduct, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end MathlibExtTest.DeterminantLemma
