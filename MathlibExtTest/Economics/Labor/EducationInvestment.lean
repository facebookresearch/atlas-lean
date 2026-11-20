/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Labor.EducationInvestment
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section

namespace MathlibExtTest.Economics.Labor.EducationInvestment

open MathlibExt.Economics.EducationInvestment

/-- Wage stream with education: schooling in period 0, wage 30 afterwards. -/
noncomputable def wE : ℕ → ℝ := fun t => if t = 1 ∨ t = 2 then 30 else 0

/-- Wage stream without education: wage 10 in each in-horizon period. -/
noncomputable def wN : ℕ → ℝ := fun t => if t < 3 then 10 else 0

/-- Direct schooling cost stream: upfront cost 4 in period 0. -/
noncomputable def cCost : ℕ → ℝ := fun t => if t = 0 then 4 else 0

/-- Boundary cost stream: upfront cost 5 in period 0 (indifference case). -/
noncomputable def cCost5 : ℕ → ℝ := fun t => if t = 0 then 5 else 0

theorem pv_incr_eq : presentValue 1 3 (fun t => wE t - wN t) = 5 := by
  simp only [presentValue, Finset.sum_range_succ, Finset.sum_range_zero, wE, wN]
  norm_num

theorem pv_cost_eq : presentValue 1 3 cCost = 4 := by
  simp only [presentValue, Finset.sum_range_succ, Finset.sum_range_zero, cCost]
  norm_num

theorem prefers_test : PrefersEducation 1 3 wE wN cCost := by
  rw [prefersEducation_iff, pv_incr_eq, pv_cost_eq]
  norm_num

theorem pv_cost5_eq : presentValue 1 3 cCost5 = 5 := by
  simp only [presentValue, Finset.sum_range_succ, Finset.sum_range_zero, cCost5]
  norm_num

theorem boundary_not_prefers : ¬ PrefersEducation 1 3 wE wN cCost5 := by
  rw [prefersEducation_iff, pv_incr_eq, pv_cost5_eq]
  norm_num

theorem boundary_weak_le :
    valueWithoutEducation 1 3 wN ≤ valueWithEducation 1 3 wE cCost5 := by
  rw [valueWithout_le_valueWith_iff, pv_incr_eq, pv_cost5_eq]

end MathlibExtTest.Economics.Labor.EducationInvestment