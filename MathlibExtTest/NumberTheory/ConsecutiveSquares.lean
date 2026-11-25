/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ConsecutiveSquares

open MetaMathlibExt

-- The 3-4-5 solution has the smallest possible positive denominator.
example : 1 < (2 : ℝ) ∧ (2 : ℝ) < 1 + 2 ^ (1 / 3 : ℝ) + 2 ^ (2 / 3 : ℝ) := by
  convert soCS_ratio_bounds 2 4 5 isSoCSSolution_two_four_five using 1 <;> norm_num

-- A solution with a nonintegral ratio exercises division in ℝ.
example : 1 < (17 / 8 : ℝ) ∧ (17 / 8 : ℝ) < 1 + 2 ^ (1 / 3 : ℝ) + 2 ^ (2 / 3 : ℝ) := by
  have h : IsSoCSSolution 17 34 42 := by norm_num [IsSoCSSolution, SoCSEq]
  convert soCS_ratio_bounds 17 34 42 h using 1 <;> norm_num

-- Equal endpoints satisfy the polynomial equation and violate the solution inequalities.
example (b : ℤ) : SoCSEq b b b ∧ ¬ IsSoCSSolution b b b := by
  constructor
  · unfold SoCSEq
    ring
  · exact fun h => (lt_irrefl b) h.2.2.1
