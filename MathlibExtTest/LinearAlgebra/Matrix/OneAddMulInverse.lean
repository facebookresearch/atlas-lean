/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.OneAddMulInverse
import Mathlib.Algebra.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-! # Tests for invertibility and inverses of `1 + A * B` -/

open Matrix
open MetaMathlibExt.Matrix

namespace MathlibExtTest.OneAddMulInverse

private def rectA : Matrix (Fin 2) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0]
private def rectB : Matrix (Fin 3) (Fin 2) ℚ := !![1, 1; 0, 2; 3, 4]

/-- The two invertible matrices have sizes `2 × 2` and `3 × 3`, respectively. -/
example : IsUnit (1 + rectB * rectA) ∧
    rectB * (1 + rectA * rectB)⁻¹ = (1 + rectB * rectA)⁻¹ * rectB := by
  have h : IsUnit (1 + rectA * rectB) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two]
    norm_num [rectA, rectB, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_three]
  exact ⟨(isUnit_one_add_mul_comm rectA rectB).mp h, mul_nonsing_inv_one_add_mul rectA rectB⟩

private def squareA : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]
private def squareB : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]

/-- The invertible case does not require the two matrix factors to commute. -/
example : squareA * squareB ≠ squareB * squareA ∧ IsUnit (1 + squareA * squareB) ∧
    squareB * (1 + squareA * squareB)⁻¹ = (1 + squareB * squareA)⁻¹ * squareB := by
  refine ⟨?_, ?_, mul_nonsing_inv_one_add_mul squareA squareB⟩
  · have h01 : (squareA * squareB) 0 1 ≠ (squareB * squareA) 0 1 :=
      by norm_num [squareA, squareB, Matrix.mul_apply, Fin.sum_univ_two]
    exact fun h => h01 (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) h)
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two]
    norm_num [squareA, squareB, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

private def singularA : Matrix (Fin 1) (Fin 2) ℚ := !![1, 2]
private def singularB : Matrix (Fin 2) (Fin 1) ℚ := !![1; -1]

/-- Here `1 + A * B` is the zero `1 × 1` matrix, while `1 + B * A` is a nonzero
singular `2 × 2` matrix. The inverse identity holds without a unit hypothesis. -/
example : ¬IsUnit (1 + singularA * singularB) ∧ ¬IsUnit (1 + singularB * singularA) ∧
    singularB * (1 + singularA * singularB)⁻¹ = (1 + singularB * singularA)⁻¹ * singularB := by
  have h : ¬IsUnit (1 + singularA * singularB) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_one]
    norm_num [singularA, singularB, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_two]
  exact ⟨h, mt (isUnit_one_add_mul_comm singularA singularB).mpr h,
    mul_nonsing_inv_one_add_mul singularA singularB⟩

end MathlibExtTest.OneAddMulInverse
