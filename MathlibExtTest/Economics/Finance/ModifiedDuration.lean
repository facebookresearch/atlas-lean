/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.ModifiedDuration
import Mathlib.Tactic.NormNum

/-!
# Tests for modified duration

A single payment of `100` at date `1` costs `100` at yield `0`, has modified
duration `1`, and price derivative `-100` there, as `P′ = -Dmod * P` says. The
same holds for the FI03.T02 price `cashFlowPrice`, and FI03.T02's monotonicity
applies to `yieldPrice` through `yieldPrice_eq_cashFlowPrice`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.ModifiedDuration

open MathlibExt.Economics.Finance

-- Test section (required): concrete evaluations with all hypotheses proved.

/-- Single payment of `100` at date `1` costs `100` at yield `0`. -/
example : yieldPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 100 := by
  unfold yieldPrice
  simp

/-- Its modified duration at yield `0` is `1`. -/
example : modifiedDuration (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 1 := by
  unfold modifiedDuration macaulayDuration yieldPrice
  simp

/-- Its price derivative at yield `0` is `-100`, via the pinned theorem. -/
example : deriv (yieldPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1}) 0 = -100 := by
  have hr : (-1 : ℝ) < 0 := by norm_num
  have hY : yieldPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 100 := by
    unfold yieldPrice
    simp
  have hP : yieldPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 ≠ 0 := by
    rw [hY]
    norm_num
  have h := deriv_yieldPrice_eq_neg_modifiedDuration_mul hr hP
  rw [h]
  have hM : modifiedDuration (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 1 := by
    unfold modifiedDuration macaulayDuration yieldPrice
    simp
  rw [hM, hY]
  norm_num

/-- The FI03.T02 price `cashFlowPrice` of the same payment has derivative `-100`
at yield `0`, via the `cashFlowPrice` form of the theorem. -/
example : deriv (cashFlowPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1}) 0 = -100 := by
  have hC : cashFlowPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 100 := by
    unfold cashFlowPrice presentValue discountFactor
    simp
  have hM : modifiedDuration (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 1 := by
    unfold modifiedDuration macaulayDuration yieldPrice
    simp
  rw [deriv_cashFlowPrice_eq_neg_modifiedDuration_mul (by norm_num) (by rw [hC]; norm_num),
    hM, hC]
  norm_num

/-- FI03.T02's strict monotonicity applies to `yieldPrice` through
`yieldPrice_eq_cashFlowPrice`. -/
example :
    StrictAntiOn (yieldPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1}) (Set.Ioi (-1)) := by
  rw [yieldPrice_eq_cashFlowPrice]
  refine strictAntiOn_cashFlowPrice ?_ ⟨1, by simp, le_rfl, by norm_num⟩
  intro t ht
  simp only [Finset.mem_singleton] at ht
  subst ht
  norm_num

end MathlibExtTest.Economics.Finance.ModifiedDuration
