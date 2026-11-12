/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# The DuPont decomposition of return on equity (Atlas AC03.T03)

Profit margin, asset turnover and equity multiplier, all computed from one consistent
set of balances, multiply to return on equity when sales and total assets are nonzero.
The proof is two applications of `div_mul_div_cancel₀`.

## Main results

* `MathlibExt.Economics.Accounting.DuPontInputs.profitMargin_mul_assetTurnover_mul_equityMultiplier`

## References

* OpenStax, *Principles of Finance*, §6.6 (profitability ratios and the DuPont method).
-/

namespace MathlibExt.Economics.Accounting

/-- Inputs of a DuPont decomposition: net income and sales for the period, and total
assets and shareholders' equity measured on one consistent basis (e.g. both average or
both ending balances). -/
structure DuPontInputs where
  /-- Net income for the period. -/
  netIncome : ℝ
  /-- Sales (revenue) for the period. -/
  sales : ℝ
  /-- Total assets on the chosen balance basis. -/
  totalAssets : ℝ
  /-- Shareholders' equity on the same balance basis. -/
  equity : ℝ

namespace DuPontInputs

/-- Net profit margin: net income over sales. -/
noncomputable def profitMargin (d : DuPontInputs) : ℝ :=
  d.netIncome / d.sales

/-- Asset turnover: sales over total assets. -/
noncomputable def assetTurnover (d : DuPontInputs) : ℝ :=
  d.sales / d.totalAssets

/-- Equity multiplier (financial leverage): total assets over equity. -/
noncomputable def equityMultiplier (d : DuPontInputs) : ℝ :=
  d.totalAssets / d.equity

/-- Return on equity: net income over equity. -/
noncomputable def returnOnEquity (d : DuPontInputs) : ℝ :=
  d.netIncome / d.equity

/-- Three-factor DuPont identity: with nonzero sales and total assets, profit margin times
asset turnover times equity multiplier equals return on equity. -/
theorem profitMargin_mul_assetTurnover_mul_equityMultiplier (d : DuPontInputs)
    (hs : d.sales ≠ 0) (ha : d.totalAssets ≠ 0) :
    d.profitMargin * d.assetTurnover * d.equityMultiplier = d.returnOnEquity := by
  unfold profitMargin assetTurnover equityMultiplier returnOnEquity
  rw [div_mul_div_cancel₀ hs, div_mul_div_cancel₀ ha]

end DuPontInputs

end MathlibExt.Economics.Accounting
