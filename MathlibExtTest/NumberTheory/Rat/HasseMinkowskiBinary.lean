/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.HasseMinkowskiBinary

/-! # Tests for `MathlibExt.NumberTheory.Rat.HasseMinkowskiBinary` -/

namespace MathlibExtTest.HasseMinkowskiBinary

-- `x² - y²` has the zero `(1, 1)` at every place, and the theorem returns a rational zero.
example : ∃ x y : ℚ, (x, y) ≠ (0, 0) ∧ 1 * x ^ 2 + (-1) * y ^ 2 = 0 :=
  Rat.exists_binary_eq_zero_of_forall_local ⟨1, 1, by simp, by norm_num⟩
    fun _ _ => ⟨1, 1, by simp, by push_cast; ring⟩

-- `3x² - 12y²` has the zero `(2, 1)` at every place.
example : ∃ x y : ℚ, (x, y) ≠ (0, 0) ∧ 3 * x ^ 2 + (-12) * y ^ 2 = 0 :=
  Rat.exists_binary_eq_zero_of_forall_local ⟨2, 1, by simp, by norm_num⟩
    fun _ _ => ⟨2, 1, by simp, by push_cast; ring⟩

end MathlibExtTest.HasseMinkowskiBinary
