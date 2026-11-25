/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IntegerComplexityLogBound

open MathlibExt.NumberTheory.IntegerComplexityWanted

-- The lower bound is sharp at the smallest positive integer.
example : Real.logb 2 (1 + 1) = (cx 1 : ℝ) := by
  apply le_antisymm
  · simpa only [Nat.cast_one] using logb_two_add_one_le 1 le_rfl
  · norm_num [show cx 1 = 1 from IntegerComplexity.complexity_one,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

-- At two the logarithm lies above one, forcing at least two occurrences of one.
example : cx 2 = 2 := by
  apply Nat.le_antisymm (IntegerComplexity.complexity_le (e := .add .one .one) rfl)
  have h : (1 : ℝ) < Real.logb 2 (1 + (2 : ℕ)) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    norm_num
  exact_mod_cast h.trans_le (logb_two_add_one_le 2 (by decide))
