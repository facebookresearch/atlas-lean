/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.HasseMinkowski

/-! # Tests for `MathlibExt.NumberTheory.Rat.HasseMinkowski` -/

namespace MathlibExtTest.HasseMinkowski

open Matrix

-- A diagonal form in five variables, `x₁² + x₂² + x₃² + x₄² - 4x₅²`, with the local zero
-- `(1, 1, 1, 1, 1)` at every place, has a rational zero.
example : ∃ x : Fin 5 → ℚ, x ≠ 0 ∧ ∑ i, ![1, 1, 1, 1, -4] i * x i ^ 2 = 0 := by
  refine (Rat.exists_diagonal_eq_zero_iff_forall_local _).2 ⟨⟨fun _ => 1, ?_, ?_⟩, fun p _ =>
    ⟨fun _ => 1, ?_, ?_⟩⟩
  · exact Function.ne_iff.2 ⟨0, by simp⟩
  · simp [Fin.sum_univ_five]; norm_num
  · exact Function.ne_iff.2 ⟨0, by simp⟩
  · simp [Fin.sum_univ_five]; norm_num

-- `x² + y² = 5` is solvable at every place (by `(1, 2)`), hence over `ℚ`.
example : ∃ x : Fin 2 → ℚ, ∑ i, ![1, 1] i * x i ^ 2 = 5 := by
  refine (Rat.exists_diagonal_eq_iff_forall_local _ (by decide) 5).2
    ⟨⟨![1, 2], ?_⟩, fun p _ => ⟨![1, 2], ?_⟩⟩
  · simp [Fin.sum_univ_two]; norm_num
  · simp [Fin.sum_univ_two]; norm_num

-- The form `2xy` of the symmetric matrix `!![0, 1; 1, 0]` has the zero `(1, 0)` everywhere.
example : ∃ x : Fin 2 → ℚ, x ≠ 0 ∧ ∑ i, ∑ j, !![0, 1; 1, 0] i j * x i * x j = 0 := by
  refine (Rat.exists_quadratic_eq_zero_iff_forall_local _).2 ⟨⟨![1, 0], ?_, ?_⟩, fun p _ =>
    ⟨![1, 0], ?_, ?_⟩⟩ <;> simp [Fin.sum_univ_two]

-- The nondegenerate form `x² + 2xy + 3y²` (matrix `!![1, 1; 1, 3]`) takes the value `6` at
-- `(1, 1)` over every completion, hence over `ℚ`.
example : ∃ x : Fin 2 → ℚ, ∑ i, ∑ j, !![1, 1; 1, 3] i j * x i * x j = 6 := by
  refine (Rat.exists_quadratic_eq_iff_forall_local _ ?_ ?_ 6).2 ⟨⟨![1, 1], ?_⟩, fun p _ =>
    ⟨![1, 1], ?_⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · simp [det_fin_two]; norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · simp [Fin.sum_univ_two]; norm_num

end MathlibExtTest.HasseMinkowski
