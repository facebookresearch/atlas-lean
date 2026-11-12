/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.ParSwapRate
import Mathlib.Tactic.NormNum

/-!
# Tests for the par swap rate

For `D t = (1/2)^t` and `T = 2`: the par rate is `1`, the floating leg is
`3 / 4`, and the fixed leg at the par rate equals the floating leg.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.ParSwapRate

open MathlibExt.Economics.Finance

-- Test section (required): concrete evaluations with all hypotheses proved.

/-- The payment-date set for `T = 2` is `{1, 2}`. -/
private theorem icc12 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Par rate for `D t = (1/2)^t`, `T = 2` equals `1`. -/
example : parSwapRate (fun t => ((1 / 2 : ℝ)) ^ t) 2 = 1 := by
  unfold parSwapRate
  rw [icc12, Finset.sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) by decide),
    Finset.sum_singleton]
  norm_num

/-- Floating leg for `D t = (1/2)^t`, `T = 2` equals `3 / 4`. -/
example : swapFloatingLeg (fun t => ((1 / 2 : ℝ)) ^ t) 2 = 3 / 4 := by
  unfold swapFloatingLeg
  rw [icc12, Finset.sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) by decide),
    Finset.sum_singleton]
  norm_num

/-- Fixed leg at par equals floating leg, via the pinned theorem. -/
example : swapFixedLeg
    (parSwapRate (fun t => ((1 / 2 : ℝ)) ^ t) 2)
    (fun t => ((1 / 2 : ℝ)) ^ t) 2
    = swapFloatingLeg (fun t => ((1 / 2 : ℝ)) ^ t) 2 := by
  apply parSwapRate_eq_fixed_eq_floating
  · show ((1 / 2 : ℝ) ^ (0 : ℕ)) = 1
    norm_num
  · rw [icc12, Finset.sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) by decide),
      Finset.sum_singleton]
    norm_num

end MathlibExtTest.Economics.Finance.ParSwapRate
