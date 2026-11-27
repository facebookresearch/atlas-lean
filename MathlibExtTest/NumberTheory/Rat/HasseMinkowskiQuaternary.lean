/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.HasseMinkowskiQuaternary

/-!
# Tests for the Hasse–Minkowski theorem for diagonal quaternary forms over `ℚ`
-/

set_option autoImplicit false

namespace HasseMinkowskiQuaternaryTest

/-- The form `x₁ ^ 2 + x₂ ^ 2 - x₃ ^ 2 - x₄ ^ 2` has the local zero `(1, 0, 1, 0)` everywhere, and
the theorem returns a rational zero. -/
example : ∃ x₁ x₂ x₃ x₄ : ℚ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
    1 * x₁ ^ 2 + 1 * x₂ ^ 2 + (-1) * x₃ ^ 2 + (-1) * x₄ ^ 2 = 0 :=
  Rat.exists_quaternary_eq_zero_of_forall_local one_ne_zero one_ne_zero (by norm_num)
    (by norm_num) ⟨1, 0, 1, 0, by norm_num, by norm_num⟩
    (fun _ _ => ⟨1, 0, 1, 0, by simp, by push_cast; ring⟩)

/-- The form `x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 - 3 x₄ ^ 2` has the local zero `(1, 1, 1, 1)` everywhere,
and the theorem returns a rational zero. -/
example : ∃ x₁ x₂ x₃ x₄ : ℚ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
    1 * x₁ ^ 2 + 1 * x₂ ^ 2 + 1 * x₃ ^ 2 + (-3) * x₄ ^ 2 = 0 :=
  Rat.exists_quaternary_eq_zero_of_forall_local one_ne_zero one_ne_zero one_ne_zero
    (by norm_num) ⟨1, 1, 1, 1, by norm_num, by norm_num⟩
    (fun _ _ => ⟨1, 1, 1, 1, by simp, by push_cast; ring⟩)

/-- The general statement, with local solvability as hypotheses. -/
example {a₁ a₂ a₃ a₄ : ℚ} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0)
    (hreal : ∃ x₁ x₂ x₃ x₄ : ℝ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
      (a₁ : ℝ) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ x₁ x₂ x₃ x₄ : ℚ_[p],
      ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
      (a₁ : ℚ_[p]) * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0) :
    ∃ x₁ x₂ x₃ x₄ : ℚ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0) ∧
      a₁ * x₁ ^ 2 + a₂ * x₂ ^ 2 + a₃ * x₃ ^ 2 + a₄ * x₄ ^ 2 = 0 :=
  Rat.exists_quaternary_eq_zero_of_forall_local h₁ h₂ h₃ h₄ hreal hpadic

end HasseMinkowskiQuaternaryTest
