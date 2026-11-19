/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Trade.Tariff
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.Economics.Trade.Tariff` (Atlas AP01.T02). -/

namespace MathlibExtTest.Economics.Trade.Tariff

open MathlibExt.Economics.Tariff

/-- Test market: `a = 100, b = 2, c = 10, d = 1`. -/
def mkt : LinearMarket := ⟨100, 2, 10, 1, by norm_num, by norm_num⟩

theorem mkt_b : mkt.b = 2 := rfl

theorem mkt_d : mkt.d = 1 := rfl

/-- At price 25, supply is 35. -/
example : supply mkt 25 = 35 := by
  simp only [mkt, supply]
  norm_num

/-- At price 25, demand is 50. -/
example : demand mkt 25 = 50 := by
  simp only [mkt, demand]
  norm_num

/-- Regime hypothesis at the tariff-inclusive price `20 + 5`. -/
example : supply mkt (20 + 5) ≤ demand mkt (20 + 5) := by
  simp only [mkt, supply, demand]
  norm_num

/-- Imports fall by 15 when the tariff is imposed. -/
example : imports mkt 20 - imports mkt 25 = 15 := by
  have ht : (0 : ℝ) ≤ 5 := by norm_num
  have hint : supply mkt (20 + 5) ≤ demand mkt (20 + 5) := by
    simp only [mkt, supply, demand]
    norm_num
  have h25 : (20 : ℝ) + 5 = 25 := by norm_num
  have h := imports_sub_tariff (m := mkt) (Pw := 20) (t := 5) ht hint
  rw [mkt_b, mkt_d, h25] at h
  norm_num at h
  exact h

/-- The total welfare change is `-75/2`. -/
example : consumerSurplusChange mkt 20 5 + producerSurplusChange mkt 20 5
    + tariffRevenue mkt 20 5 = -75 / 2 := by
  have ht : (0 : ℝ) ≤ 5 := by norm_num
  have hint : supply mkt (20 + 5) ≤ demand mkt (20 + 5) := by
    simp only [mkt, supply, demand]
    norm_num
  have h := welfare_change_tariff (m := mkt) (Pw := 20) (t := 5) ht hint
  rw [mkt_b, mkt_d] at h
  norm_num at h
  linear_combination h

end MathlibExtTest.Economics.Trade.Tariff
