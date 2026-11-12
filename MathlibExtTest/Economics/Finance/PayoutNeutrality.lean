/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.PayoutNeutrality
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.PayoutNeutrality

open MathlibExt.Economics.Finance.PayoutNeutrality

-- N = 100, P = 20, C = 200: dividend per share 2, ex-div price 18.
example : dividendTotal 100 20 200 = 2000 := by
  have hN : (0:ℝ) < 100 := by norm_num
  have hC : (200:ℝ) ≤ 100 * 20 := by norm_num
  have h := (dividend_neutrality hN hC).1
  norm_num at h
  exact h

example : (0:ℝ) ≤ 20 - 200 / 100 := by
  have hN : (0:ℝ) < 100 := by norm_num
  have hC : (200:ℝ) ≤ 100 * 20 := by norm_num
  exact (dividend_neutrality hN hC).2

-- N = 100, P = 20, C = 200: repurchase buys 10 shares, 90 remain.
example : repurchaseTotal 100 20 200 = 2000 := by
  have hP : (0:ℝ) < 20 := by norm_num
  have hC0 : (0:ℝ) ≤ 200 := by norm_num
  have hC : (200:ℝ) ≤ 100 * 20 := by norm_num
  have h := (repurchase_neutrality hP hC0 hC).1
  norm_num at h
  exact h

example : (0:ℝ) ≤ 100 - 200 / 20 := by
  have hP : (0:ℝ) < 20 := by norm_num
  have hC0 : (0:ℝ) ≤ 200 := by norm_num
  have hC : (200:ℝ) ≤ 100 * 20 := by norm_num
  exact (repurchase_neutrality hP hC0 hC).2

example : dividendTotal 100 20 200 = repurchaseTotal 100 20 200 := by
  have hN : (0:ℝ) < 100 := by norm_num
  have hP : (0:ℝ) < 20 := by norm_num
  have hC0 : (0:ℝ) ≤ 200 := by norm_num
  have hC : (200:ℝ) ≤ 100 * 20 := by norm_num
  exact payout_form_neutrality hN hP hC0 hC

-- Full payout: with C = N * P both totals are N * P.
example {N P : ℝ} (hN : 0 < N) : dividendTotal N P (N * P) = N * P :=
  (dividend_neutrality hN le_rfl).1

example {N P : ℝ} (hP : 0 < P) (hC0 : 0 ≤ N * P) :
    repurchaseTotal N P (N * P) = N * P :=
  (repurchase_neutrality hP hC0 le_rfl).1

end MathlibExtTest.Economics.Finance.PayoutNeutrality
