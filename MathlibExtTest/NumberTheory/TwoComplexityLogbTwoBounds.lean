/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexityLogbTwoBounds

open MathlibExt.NumberTheory.TwoComplexityWanted

-- The base case is tight on both sides.
example : complexityL 2 2 = 1 := by
  have h := logb_two_bounds 2 (by decide) (by decide)
  norm_num [Real.logb_self_eq_one] at h
  exact le_antisymm h.2 h.1

-- For 4 the half is again even.
example : 2 ≤ complexityL 2 4 ∧ complexityL 2 4 ≤ 3 := by
  have hlog : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
    norm_num [Real.logb_self_eq_one]
  have h := logb_two_bounds 4 (by decide) (by decide)
  rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, hlog] at h
  norm_num at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

-- For 6 the half is odd, so the construction uses an extra copy of 2.
example : 2 < complexityL 2 6 ∧ (complexityL 2 6 : ℝ) ≤ 2 * Real.logb 2 6 - 1 := by
  have h := logb_two_bounds 6 (by decide) (by decide)
  have hlog : (2 : ℝ) < Real.logb 2 (6 : ℕ) := by
    calc
      (2 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        norm_num
      _ < Real.logb 2 (6 : ℕ) := Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by exact_mod_cast hlog.trans_le h.1, by simpa only [Nat.cast_ofNat] using h.2⟩
