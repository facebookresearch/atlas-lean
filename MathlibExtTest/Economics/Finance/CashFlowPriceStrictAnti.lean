/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.CashFlowPriceStrictAnti
import Mathlib.Tactic.NormNum

/-!
# Tests for strictly decreasing cash-flow prices

A single payment of `100` at date `1` costs `100` at yield `0` and `50` at
yield `1`, so the price at yield `1` is below the price at yield `0`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.CashFlowPriceStrictAnti

open MathlibExt.Economics.Finance

-- Test section (required): concrete evaluations with all hypotheses proved.

/-- Single payment of `100` at date `1`. -/
private def testCash : ℕ → ℝ := fun t => if t = 1 then 100 else 0

example : cashFlowPrice testCash {1} 0 = 100 := by
  simp [cashFlowPrice, presentValue, discountFactor, testCash]

example : cashFlowPrice testCash {1} 1 = 50 := by
  simp [cashFlowPrice, presentValue, discountFactor, testCash]
  norm_num

example : cashFlowPrice testCash {1} 1 < cashFlowPrice testCash {1} 0 := by
  have h1 : testCash 1 = (100 : ℝ) := by simp [testCash]
  have hnn : ∀ t ∈ ({1} : Finset ℕ), 0 ≤ testCash t := by
    intro t ht
    rw [Finset.mem_singleton.mp ht, h1]
    norm_num
  have hpos : ∃ t ∈ ({1} : Finset ℕ), 1 ≤ t ∧ 0 < testCash t := by
    refine ⟨1, by simp, le_refl 1, ?_⟩
    rw [h1]
    norm_num
  have hm0 : (0 : ℝ) ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; norm_num
  have hm1 : (1 : ℝ) ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; norm_num
  have h01 : (0 : ℝ) < 1 := by norm_num
  exact strictAntiOn_cashFlowPrice hnn hpos hm0 hm1 h01

end MathlibExtTest.Economics.Finance.CashFlowPriceStrictAnti
