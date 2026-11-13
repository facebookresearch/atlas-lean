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
duration `1`, and price derivative `-100` there, as `P′ = -Dmod * P` says.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.ModifiedDuration

open MathlibExt.Economics.Finance

-- Test section (required): concrete evaluations with all hypotheses proved.

/-- Single payment of `100` at date `1` costs `100` at yield `0`. -/
example : cashFlowPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 100 := by
  unfold cashFlowPrice presentValue discountFactor
  simp

/-- Its modified duration at yield `0` is `1`. -/
example : modifiedDuration (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 1 := by
  unfold modifiedDuration macaulayDuration cashFlowPrice presentValue discountFactor
  simp

/-- Its price derivative at yield `0` is `-100`, via the pinned theorem. -/
example : deriv (cashFlowPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1}) 0 = -100 := by
  have hC : cashFlowPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 100 := by
    unfold cashFlowPrice presentValue discountFactor
    simp
  have hM : modifiedDuration (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 = 1 := by
    unfold modifiedDuration macaulayDuration cashFlowPrice presentValue discountFactor
    simp
  rw [deriv_cashFlowPrice_eq_neg_modifiedDuration_mul (by norm_num) (by rw [hC]; norm_num),
    hM, hC]
  norm_num

end MathlibExtTest.Economics.Finance.ModifiedDuration
