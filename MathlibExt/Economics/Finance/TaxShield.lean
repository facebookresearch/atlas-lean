/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import MathlibExt.Economics.Finance.GrowingPerpetuity

/-!
# Perpetual riskless-debt tax shield

A specified perpetual riskless-debt tax-shield model has shield value `τ * D`:
in each period the firm deducts interest `rD * D` at tax rate `τ`, saving
`τ * rD * D`, discounted at the riskless rate `rD`. The result is a
specialization of the landed growing-perpetuity formula `growingPerpetuity_eq`
at growth `g = 0`: the shield sum is the growing-perpetuity sum with first
payment `τ * rD * D`, and the formula gives `τ * rD * D / rD = τ * D`.

Model assumptions (not proved): debt is perpetual and riskless, `rD` and `τ`
are constant, interest is deducted in full every period, and the shield is
discounted at `rD`. No claim is made about risky debt or finite maturity.

## Main results

* `MathlibExt.Economics.Finance.TaxShield.perpetual_taxShield_value`: the
  perpetual tax shield is worth `τ * D` when `0 < rD`.

## References

F. Modigliani and M. H. Miller, "The Cost of Capital, Corporation Finance and
the Theory of Investment", American Economic Review 48(3), 1958; M. J. Gordon,
"The Investment, Financing, and Valuation of the Corporation" (growth formula),
1962. Atlas roadmap target FI09.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.TaxShield

/-- Present value of the perpetual tax shield on riskless debt: in each period
`t = 1, 2, …` the firm deducts interest `rD * D` at tax rate `τ`, saving
`τ * rD * D`, discounted at the riskless rate `rD`. The `n`-th summand is the
period-`n + 1` shield discounted by `(1 + rD)⁻¹ ^ (n + 1)`. -/
noncomputable def taxShieldValue (τ rD D : ℝ) : ℝ :=
  ∑' n : ℕ, τ * rD * D * ((1 + rD)⁻¹) ^ (n + 1)

/-- **Perpetual riskless-debt tax shield.** Under the discounting assumptions of
`taxShieldValue` (perpetual debt, constant riskless rate `rD > 0`, constant tax rate,
interest deducted every period), the shield value is `τ * D`. The proof is a
specialization of the landed `growingPerpetuity_eq` at growth `g = 0`: the shield
sum equals `growingPerpetuity (τ * rD * D) rD 0`, and the Gordon-growth formula
gives `τ * rD * D / rD = τ * D`. -/
theorem perpetual_taxShield_value {τ rD D : ℝ} (hrD : 0 < rD) :
    taxShieldValue τ rD D = τ * D := by
  have h1 : (0:ℝ) < 1 + rD := by linarith
  have h2 : (0:ℝ) ≤ (1 + 0) / (1 + rD) := div_nonneg (by linarith) h1.le
  have h3 : (1 + 0) / (1 + rD) < (1:ℝ) := by
    rw [add_zero, div_lt_one h1]
    linarith
  have hEq : taxShieldValue τ rD D = growingPerpetuity (τ * rD * D) rD 0 := by
    unfold taxShieldValue growingPerpetuity
    apply tsum_congr
    intro n
    simp only [growingPerpetuityTerm, discountFactor, add_zero, one_pow, mul_one,
      inv_pow]
    ring
  have hGP : growingPerpetuity (τ * rD * D) rD 0 = (τ * rD * D) / (rD - 0) :=
    growingPerpetuity_eq (τ * rD * D) rD 0 h1 h2 h3
  have hrDne : rD ≠ 0 := ne_of_gt hrD
  rw [hEq, hGP, sub_zero]
  field_simp

end MathlibExt.Economics.Finance.TaxShield
