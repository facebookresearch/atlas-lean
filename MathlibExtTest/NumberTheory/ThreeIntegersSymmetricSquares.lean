/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquares

/-! # Tests for quotients of sums of two rational squares -/

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

example : IsSumTwoSquaresℚ 0 :=
  ⟨0, 0, by norm_num⟩

-- The denominator can be nonintegral and a square summand can vanish.
example : IsSumTwoSquaresℚ (1 / (5 / 9)) :=
  sum_two_squares_div_sum_two_squaresℚ (by norm_num) (by norm_num)
    ⟨1, 0, by norm_num⟩ ⟨1 / 3, -2 / 3, by norm_num⟩

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
