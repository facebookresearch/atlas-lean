/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Padics.TernaryIsotropic

namespace TernaryIsotropicTest

/-- Consumer with the original binders and hypotheses. -/
theorem exactSource
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 :=
  Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two p hp a b ha hb

/-- Concrete instance at `p = 3`, `a = b = 1`. -/
example : ∃ z x y : ℚ_[3], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
    z ^ 2 - (1 : ℚ_[3]) * x ^ 2 - (1 : ℚ_[3]) * y ^ 2 = 0 :=
  exactSource 3 (by norm_num) 1 1 (by simp) (by simp)

end TernaryIsotropicTest
