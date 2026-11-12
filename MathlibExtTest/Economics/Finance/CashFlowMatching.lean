/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.CashFlowMatching
import Mathlib.Tactic

/-!
# Tests for exact cash-flow matching

Matched flows give surplus zero under three different discount curves
(constant `1/2`, geometric `(1/2)^t`, constant `3`); an unmatched pair gives
surplus `2`, so the theorem is not vacuous.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.CashFlowMatching

open _root_.MathlibExt.Economics.Finance.CashFlowMatching

theorem matched_example : cashFlowSurplus (fun _ => (1 / 2 : ℝ)) {0, 1, 2} (fun t => ((t : ℝ) + 1)) (fun t => ((t : ℝ) + 1)) = 0 := by
  apply cashFlowSurplus_eq_zero_of_matched
  intro t _
  rfl

theorem matched_discount_pow : cashFlowSurplus (fun t => (1 / 2 : ℝ) ^ t) {0, 1, 2} (fun t => ((t : ℝ) + 1)) (fun t => ((t : ℝ) + 1)) = 0 := by
  apply cashFlowSurplus_eq_zero_of_matched
  intro t _
  rfl

theorem matched_discount_const3 : cashFlowSurplus (fun _ => (3 : ℝ)) {0, 1, 2} (fun t => ((t : ℝ) + 1)) (fun t => ((t : ℝ) + 1)) = 0 := by
  apply cashFlowSurplus_eq_zero_of_matched
  intro t _
  rfl

theorem unmatched_control : cashFlowSurplus (fun _ => (1 : ℝ)) {0} (fun _ => 5) (fun _ => 3) = 2 := by
  simp only [cashFlowSurplus, Finset.sum_singleton, one_mul]
  norm_num

end MathlibExtTest.Economics.Finance.CashFlowMatching
