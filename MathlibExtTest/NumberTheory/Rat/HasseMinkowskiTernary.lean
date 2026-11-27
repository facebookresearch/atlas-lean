/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.HasseMinkowskiTernary

/-!
# Tests for the Hasse–Minkowski theorem for diagonal ternary forms over `ℚ`
-/

set_option autoImplicit false

namespace HasseMinkowskiTernaryTest

/-- The form `x ^ 2 + y ^ 2 - 2 z ^ 2` has the local zero `(1, 1, 1)` everywhere, and the theorem
returns a rational zero. -/
example : ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ 1 * x ^ 2 + 1 * y ^ 2 + (-2) * z ^ 2 = 0 :=
  Rat.exists_ternary_eq_zero_of_forall_local one_ne_zero one_ne_zero (by norm_num)
    ⟨1, 1, 1, by norm_num, by norm_num⟩
    (fun _ _ => ⟨1, 1, 1, by simp, by push_cast; ring⟩)

/-- The general statement, with local solvability as hypotheses. -/
example {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hreal : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ (a : ℝ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 :=
  Rat.exists_ternary_eq_zero_of_forall_local ha hb hc hreal hpadic

end HasseMinkowskiTernaryTest
