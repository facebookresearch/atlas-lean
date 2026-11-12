/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem

import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for full-rank square linear systems

With `A = !![2, 0; 0, 3]` (determinant `6`, full rank) and `b = ![4, 9]`,
the unique solution is `x = ![2, 3]`, and the explicit inverse vector
`A⁻¹ *ᵥ b` equals it. The boundary case is the singular
`A = !![1, 2; 2, 4]` with the inconsistent `b = ![1, 3]`: no solution
exists, so there is no unique solution either.
-/

namespace MathlibExtTest.FullRankLinearSystem

open Matrix

/-- The `2 × 2` diagonal system has the unique solution `![2, 3]`. -/
example :
    (∃! x : Fin 2 → ℝ, !![2, 0; 0, 3] *ᵥ x = ![4, 9]) ∧
      (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![4, 9] = ![2, 3] := by
  have hinj : Function.Injective (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ).mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (by
      rw [Matrix.det_fin_two_of]
      norm_num)
  have hdet : IsUnit (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ).det :=
    isUnit_iff_ne_zero.mpr (by
      rw [Matrix.det_fin_two_of]
      norm_num)
  obtain ⟨x, hx, huniq⟩ :=
    Matrix.exists_unique_mulVec_eq hinj (![4, 9] : Fin 2 → ℝ)
  have hsol : (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![2, 3] = ![4, 9] := by
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hxeq : x = ![2, 3] := (huniq _ hsol).symm
  exact ⟨⟨x, hx, huniq⟩,
    ((Matrix.mulVec_eq_iff_inv_mulVec hdet).mp hx).symm.trans hxeq⟩

/-- Boundary: the singular system with inconsistent right-hand side has
no unique solution, because it has no solution at all. -/
example :
    ¬∃! x : Fin 2 → ℝ, !![1, 2; 2, 4] *ᵥ x = ![1, 3] := by
  rintro ⟨x, hx, -⟩
  have h0 := congr_fun hx 0
  have h1 := congr_fun hx 1
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  linarith

end MathlibExtTest.FullRankLinearSystem
