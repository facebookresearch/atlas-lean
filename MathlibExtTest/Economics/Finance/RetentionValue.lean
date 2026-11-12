/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.RetentionValue
import Mathlib.Tactic.NormNum

/-!
# Tests for retained earnings and the value of growth

Tests for retained-earnings value creation: a value-creating case (`P = 100` vs
no-growth `50`), a value-destroying case (`P = 25` vs no-growth `100/3`), and the
Gordon-form substitution.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.RetentionValue

open MathlibExt.Economics.Finance.RetentionValue

-- Test 1 (value-creating): E₁ = 10, b = 1/2, ROE = 3/10, r = 1/5.
example : retentionPrice 10 (1/2) (3/10) (1/5) = 100 := by
  unfold retentionPrice
  norm_num

example : noGrowthPrice 10 (1/5) = 50 := by
  unfold noGrowthPrice
  norm_num

example : retentionPrice 10 (1/2) (3/10) (1/5) > noGrowthPrice 10 (1/5) :=
  (retentionCreatesValue_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
    (by norm_num)

-- Test 2 (value-destroying): E₁ = 10, b = 1/2, ROE = 1/5, r = 3/10.
example : retentionPrice 10 (1/2) (1/5) (3/10) = 25 := by
  unfold retentionPrice
  norm_num

example : noGrowthPrice 10 (3/10) = 100 / 3 := by
  unfold noGrowthPrice
  norm_num

example : ¬ retentionPrice 10 (1/2) (1/5) (3/10) > noGrowthPrice 10 (3/10) := by
  rw [retentionCreatesValue_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- Test 3 (growth): g = 3/20, and the Gordon form computes to 100 on both sides.
example : retentionGrowth (1/2) (3/10) = 3/20 := by
  unfold retentionGrowth
  norm_num

example : retentionPrice 10 (1/2) (3/10) (1/5)
    = 10 * (1 - 1/2) / (1/5 - retentionGrowth (1/2) (3/10)) :=
  retentionPrice_eq_gordonForm

example : (10 * (1 - (1/2:ℝ)) / ((1/5:ℝ) - retentionGrowth (1/2) (3/10)) : ℝ) = 100 := by
  unfold retentionGrowth
  norm_num


end MathlibExtTest.Economics.Finance.RetentionValue
