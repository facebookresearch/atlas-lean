/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.DuPont
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.DuPont

open MathlibExt.Economics.Accounting

/-- Margin 1/10, turnover 1/2, multiplier 5/2, return on equity 1/8. -/
theorem test_dupont :
    (DuPontInputs.mk 10 100 200 80).profitMargin = 1 / 10 ∧
      (DuPontInputs.mk 10 100 200 80).assetTurnover = 1 / 2 ∧
      (DuPontInputs.mk 10 100 200 80).equityMultiplier = 5 / 2 ∧
      (DuPontInputs.mk 10 100 200 80).returnOnEquity = 1 / 8 := by
  unfold DuPontInputs.profitMargin DuPontInputs.assetTurnover DuPontInputs.equityMultiplier
    DuPontInputs.returnOnEquity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Using 250 for assets in the multiplier but 200 in turnover breaks the identity. -/
theorem test_inconsistent_balances_break :
    (DuPontInputs.mk 10 100 200 80).profitMargin *
        (DuPontInputs.mk 10 100 200 80).assetTurnover *
        (DuPontInputs.mk 10 100 250 80).equityMultiplier ≠
      (DuPontInputs.mk 10 100 200 80).returnOnEquity := by
  unfold DuPontInputs.profitMargin DuPontInputs.assetTurnover DuPontInputs.equityMultiplier
    DuPontInputs.returnOnEquity
  norm_num

/-- With zero sales the identity fails, so the nonzero-sales hypothesis is needed. -/
theorem test_zero_sales_breaks :
    (DuPontInputs.mk 10 0 200 80).profitMargin * (DuPontInputs.mk 10 0 200 80).assetTurnover *
        (DuPontInputs.mk 10 0 200 80).equityMultiplier ≠
      (DuPontInputs.mk 10 0 200 80).returnOnEquity := by
  unfold DuPontInputs.profitMargin DuPontInputs.assetTurnover DuPontInputs.equityMultiplier
    DuPontInputs.returnOnEquity
  norm_num

/-- The DuPont identity for net income 10, sales 100, assets 200, equity 80. -/
theorem test_dupont_identity_example :
    (DuPontInputs.mk 10 100 200 80).profitMargin * (DuPontInputs.mk 10 100 200 80).assetTurnover *
        (DuPontInputs.mk 10 100 200 80).equityMultiplier =
      (DuPontInputs.mk 10 100 200 80).returnOnEquity := by
  exact DuPontInputs.profitMargin_mul_assetTurnover_mul_equityMultiplier _ (by show (100:ℝ) ≠ 0; norm_num) (by show (200:ℝ) ≠ 0; norm_num)

/-- The identity holds for every equity value, including 0, by the main theorem. -/
theorem test_dupont_any_equity (e : ℝ) :
    (DuPontInputs.mk 10 100 200 e).profitMargin * (DuPontInputs.mk 10 100 200 e).assetTurnover *
        (DuPontInputs.mk 10 100 200 e).equityMultiplier =
      (DuPontInputs.mk 10 100 200 e).returnOnEquity := by
  exact DuPontInputs.profitMargin_mul_assetTurnover_mul_equityMultiplier _ (by show (100:ℝ) ≠ 0; norm_num) (by show (200:ℝ) ≠ 0; norm_num)

end MathlibExtTest.Economics.Accounting.DuPont
