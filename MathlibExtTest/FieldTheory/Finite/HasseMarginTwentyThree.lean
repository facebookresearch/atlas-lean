/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.HasseMarginTwentyThree

/-!
# Tests for the margin $q + 1 - 2\sqrt q > 12$ for $q \ge 23$
-/

set_option autoImplicit false

@[expose] public section

namespace HasseMarginTwentyThreeTest

/-- At $q = 23$. -/
example : 0 < (23 : ℝ) + 1 - 2 * √(23 : ℝ) - 12 :=
  Real.add_one_sub_two_mul_sqrt_sub_twelve_pos le_rfl

/-- At the prime power $q = 25$, where $q + 1 - 2\sqrt q - 12 = 4$. -/
example : 0 < ((25 : ℕ) : ℝ) + 1 - 2 * √((25 : ℕ) : ℝ) - 12 :=
  Real.natCast_add_one_sub_two_mul_sqrt_sub_twelve_pos (by norm_num)

/-- The margin as $\#X(\mathbb{F}_q) > 0$: any count bounded below by $q + 1 - 2\sqrt q - 12$ is
positive. -/
example (q : ℕ) (hq : 23 ≤ q) (N : ℝ) (hN : (q : ℝ) + 1 - 2 * √(q : ℝ) - 12 ≤ N) : 0 < N :=
  lt_of_lt_of_le (Real.natCast_add_one_sub_two_mul_sqrt_sub_twelve_pos hq) hN

#check @Real.add_one_sub_two_mul_sqrt_sub_twelve_pos
#check @Real.natCast_add_one_sub_two_mul_sqrt_sub_twelve_pos

end HasseMarginTwentyThreeTest
