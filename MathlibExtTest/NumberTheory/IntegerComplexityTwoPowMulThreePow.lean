/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Bounds.Defs
import MathlibExt.NumberTheory.IntegerComplexityTwoPowMulThreePow

open MathlibExt.NumberTheory.IntegerComplexityWanted

-- The three smallest cases: the expressions 1 + 1, 1 + (1 + 1) and (1 + 1)(1 + 1) are optimal.
example : cx 2 = 2 := complexity_two_pow_mul_three_pow 1 0 (by decide) (by decide)
example : cx 3 = 3 := complexity_two_pow_mul_three_pow 0 1 (by decide) (by decide)
example : cx 4 = 4 := complexity_two_pow_mul_three_pow 2 0 (by decide) (by decide)

-- Multiples of three, one for each exponent of two.
example : cx 9 = 6 := complexity_two_pow_mul_three_pow 0 2 (by decide) (by decide)
example : cx 6 = 5 := complexity_two_pow_mul_three_pow 1 1 (by decide) (by decide)
example : cx 12 = 7 := complexity_two_pow_mul_three_pow 2 1 (by decide) (by decide)

-- A large exponent of three, far beyond a table of complexities.
example : cx (2 ^ 2 * 3 ^ 100) = 304 :=
  complexity_two_pow_mul_three_pow 2 100 (by decide) (by decide)

-- With the extremal bound, twelve is the largest number of complexity seven.
example : IsGreatest {m | cx m = 7} 12 :=
  ⟨complexity_two_pow_mul_three_pow 2 1 (by decide) (by decide), fun m hm =>
    not_lt.mp fun h => (complexity_lt_of_gt_extremal 2 1 m (by decide) (by decide) h).ne' hm⟩

-- The excluded case `a = b = 0`: writing one takes one 1, not none.
example : cx (2 ^ 0 * 3 ^ 0) ≠ 2 * 0 + 3 * 0 := by
  rw [show cx (2 ^ 0 * 3 ^ 0) = 1 from IntegerComplexity.complexity_one]
  decide
