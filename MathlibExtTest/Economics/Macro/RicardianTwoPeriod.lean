/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.RicardianTwoPeriod
import Mathlib.Tactic.NormNum

/-!
# Tests for Ricardian tax-timing invariance

With `r = 1/10`, `g0 = 10`, `g1 = 11`, `y0 = 100`, `y1 = 110`: the tax
paths `(5, 33/2)` and `(7, 143/10)` both satisfy the government budgets,
present value of taxes is `20`, and the household present-value budget is
`180` on both paths.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.RicardianTwoPeriod

open MathlibExt.Economics.Macro.RicardianTwoPeriod

/-- Path 1 budgets with `r = 1/10`, `g0 = 10`, `g1 = 11`,
`(t0, t1) = (5, 33/2)`, `b0 = 5`. -/
theorem test_path1_budgets :
    (10 : ℝ) = 5 + 5 ∧ (11 : ℝ) + (1 + 1 / 10) * 5 = 33 / 2 := by
  constructor <;> norm_num

/-- Path 2 budgets with `r = 1/10`, `g0 = 10`, `g1 = 11`,
`(t0', t1') = (7, 143/10)`, `b0' = 3`. -/
theorem test_path2_budgets :
    (10 : ℝ) = 7 + 3 ∧ (11 : ℝ) + (1 + 1 / 10) * 3 = 143 / 10 := by
  constructor <;> norm_num

/-- Path 1 present value of taxes equals 20, via
`government_presentValue_budget`. -/
theorem test_path1_presentValue : (5 : ℝ) + (33 / 2) / (1 + 1 / 10) = 20 := by
  have h := government_presentValue_budget (r := (1 / 10 : ℝ)) (g0 := (10 : ℝ))
    (g1 := (11 : ℝ)) (t0 := (5 : ℝ)) (t1 := (33 / 2 : ℝ)) (b0 := (5 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

/-- Household present-value budgets agree on both tax paths, via
`taxTimingShift_presentValue_invariant`. -/
theorem test_household_invariant :
    (100 - 5 : ℝ) + (110 - 33 / 2) / (1 + 1 / 10)
      = (100 - 7 : ℝ) + (110 - 143 / 10) / (1 + 1 / 10) := by
  exact taxTimingShift_presentValue_invariant (r := (1 / 10 : ℝ)) (g0 := (10 : ℝ))
    (g1 := (11 : ℝ)) (t0 := (5 : ℝ)) (t1 := (33 / 2 : ℝ)) (t0' := (7 : ℝ))
    (t1' := (143 / 10 : ℝ)) (b0 := (5 : ℝ)) (b0' := (3 : ℝ)) (y0 := (100 : ℝ))
    (y1 := (110 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Household present-value budget on path 1 equals 180, via
`taxTimingShift_presentValue_invariant`. -/
theorem test_household_path1_value :
    (100 - 5 : ℝ) + (110 - 33 / 2) / (1 + 1 / 10) = 180 := by
  have h := taxTimingShift_presentValue_invariant (r := (1 / 10 : ℝ)) (g0 := (10 : ℝ))
    (g1 := (11 : ℝ)) (t0 := (5 : ℝ)) (t1 := (33 / 2 : ℝ)) (t0' := (7 : ℝ))
    (t1' := (143 / 10 : ℝ)) (b0 := (5 : ℝ)) (b0' := (3 : ℝ)) (y0 := (100 : ℝ))
    (y1 := (110 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : (100 - 7 : ℝ) + (110 - 143 / 10) / (1 + 1 / 10) = 180 := by norm_num
  rw [h]
  exact h2

/-- Household present-value budget on path 2 equals 180, via
`taxTimingShift_presentValue_invariant`. -/
theorem test_household_path2_value :
    (100 - 7 : ℝ) + (110 - 143 / 10) / (1 + 1 / 10) = 180 := by
  have h := taxTimingShift_presentValue_invariant (r := (1 / 10 : ℝ)) (g0 := (10 : ℝ))
    (g1 := (11 : ℝ)) (t0 := (5 : ℝ)) (t1 := (33 / 2 : ℝ)) (t0' := (7 : ℝ))
    (t1' := (143 / 10 : ℝ)) (b0 := (5 : ℝ)) (b0' := (3 : ℝ)) (y0 := (100 : ℝ))
    (y1 := (110 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h1 : (100 - 5 : ℝ) + (110 - 33 / 2) / (1 + 1 / 10) = 180 := by norm_num
  rw [← h]
  exact h1

end MathlibExtTest.Economics.Macro.RicardianTwoPeriod
