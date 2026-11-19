/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
import Mathlib.Tactic.NormNum

/-!
# Tests for dated cash flows and present value

At rate `r = 1` over dates `0, 1, 2`, the flows `t + 1` have present value `11/4`, the level
flows `4` have present value `7`, and linearity gives `2 · 11/4 - 7 = -3/2` for `2 c - d`.
The empty date set has present value `0`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.DatedCashFlow

open MathlibExt.Economics.Finance

example : presentValue (discountFactor 1) (Finset.range 3) (fun t : ℕ => (t : ℝ) + 1) = 11 / 4 := by
  simp [presentValue, discountFactor, Finset.sum_range_succ]
  norm_num

example : presentValue (discountFactor 1) (Finset.range 3) (fun _ : ℕ => (4 : ℝ)) = 7 := by
  simp [presentValue, discountFactor, Finset.sum_range_succ]
  norm_num

example : presentValue (discountFactor 1) (Finset.range 3) ((2 : ℝ) • (fun t : ℕ => (t : ℝ) + 1) + (-1 : ℝ) • (fun _ : ℕ => (4 : ℝ))) = -3 / 2 := by
  have h1 : presentValue (discountFactor 1) (Finset.range 3) (fun t : ℕ => (t : ℝ) + 1) = 11 / 4 := by
    simp [presentValue, discountFactor, Finset.sum_range_succ]
    norm_num
  have h2 : presentValue (discountFactor 1) (Finset.range 3) (fun _ : ℕ => (4 : ℝ)) = 7 := by
    simp [presentValue, discountFactor, Finset.sum_range_succ]
    norm_num
  rw [presentValue_linear, h1, h2]
  norm_num

example (D : ℕ → ℝ) (c : ℕ → ℝ) : presentValue D ∅ c = 0 := by
  simp [presentValue]

end MathlibExtTest.Economics.Finance.DatedCashFlow
