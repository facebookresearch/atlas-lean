/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Welfare.DeadweightLoss
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Exact triangular deadweight loss for linear schedules

With linear inverse demand `α - β q` and inverse supply `γ + δ q` (`β + δ > 0`), a per-unit tax
`τ` moves the equilibrium from `q* = (α - γ) / (β + δ)` to `q_τ = (α - γ - τ) / (β + δ)`, and the
deadweight loss `∫_{q_τ}^{q*} (Pd - Ps)` (the Atlas `deadweightLoss`) is exactly the triangle
`τ (q* - q_τ) / 2 = τ² / (2 (β + δ))`. For smooth nonlinear schedules the triangle is only the
leading term (`deadweightLoss_sub_harberger_isBigO`).

## Main results

* `isTaxEquilibrium_linear`: `q_τ` is the tax-`τ` equilibrium (`τ = 0` gives `q*`).
* `deadweightLoss_linear`: the exact triangle formula.
* `linear_interior_regime`: for `0 ≤ τ ≤ α - γ`, `0 ≤ q_τ ≤ q*` and the loss is nonnegative.

Atlas roadmap target EC09.T03.

## References

* H. R. Varian, *Intermediate Microeconomics*, 9th ed., Norton (2014), ch. 16.
-/

@[expose] public section

namespace MathlibExt.Economics.DeadweightLoss

/-- With linear inverse demand `α - β q` and inverse supply `γ + δ q` (`β + δ > 0`), the
quantity `(α - γ - τ) / (β + δ)` is the tax-`τ` equilibrium; `τ = 0` gives the no-tax
equilibrium `(α - γ) / (β + δ)`. -/
theorem isTaxEquilibrium_linear {α β γ δ τ : ℝ} (hs : 0 < β + δ) :
    IsTaxEquilibrium (fun q => α - β * q) (fun q => γ + δ * q) τ ((α - γ - τ) / (β + δ)) := by
  unfold IsTaxEquilibrium
  have hne : β + δ ≠ 0 := ne_of_gt hs
  field_simp
  ring

/-- **Exact triangular deadweight loss for linear schedules.** The lost gains from trade
between the no-tax and tax-`τ` equilibria are exactly the triangle
`τ (q* - q_τ) / 2 = τ² / (2 (β + δ))`. -/
theorem deadweightLoss_linear {α β γ δ τ : ℝ} (hs : 0 < β + δ) :
    deadweightLoss (fun q => α - β * q) (fun q => γ + δ * q) ((α - γ) / (β + δ))
        ((α - γ - τ) / (β + δ)) =
      τ * ((α - γ) / (β + δ) - (α - γ - τ) / (β + δ)) / 2 ∧
    deadweightLoss (fun q => α - β * q) (fun q => γ + δ * q) ((α - γ) / (β + δ))
        ((α - γ - τ) / (β + δ)) = τ ^ 2 / (2 * (β + δ)) := by
  have hne : β + δ ≠ 0 := ne_of_gt hs
  have hfun : ∀ x : ℝ, (α - β * x) - (γ + δ * x) = (α - γ) - (β + δ) • x := fun x => by
    simp only [smul_eq_mul]
    ring
  have h1 : IntervalIntegrable (fun _ : ℝ => α - γ) MeasureTheory.volume
      ((α - γ - τ) / (β + δ)) ((α - γ) / (β + δ)) :=
    intervalIntegrable_const
  have hid : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume
      ((α - γ - τ) / (β + δ)) ((α - γ) / (β + δ)) :=
    intervalIntegral.intervalIntegrable_id
  have h2 : IntervalIntegrable (fun x : ℝ => (β + δ) • x) MeasureTheory.volume
      ((α - γ - τ) / (β + δ)) ((α - γ) / (β + δ)) :=
    hid.const_mul _
  have hcalc : deadweightLoss (fun q => α - β * q) (fun q => γ + δ * q) ((α - γ) / (β + δ))
        ((α - γ - τ) / (β + δ))
      = (((α - γ) / (β + δ) - (α - γ - τ) / (β + δ)) * (α - γ) -
        (β + δ) * ((((α - γ) / (β + δ)) ^ 2 - ((α - γ - τ) / (β + δ)) ^ 2) / 2)) := by
    unfold deadweightLoss
    simp only [hfun]
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const,
      intervalIntegral.integral_smul, integral_id]
    simp only [smul_eq_mul]
  constructor
  · rw [hcalc]; field_simp; ring
  · rw [hcalc]; field_simp; ring

/-- **Interior-trade regime.** For a tax `0 ≤ τ ≤ α - γ`, trade stays nonnegative and the tax
reduces it, `0 ≤ q_τ ≤ q*`, and the deadweight loss is nonnegative. -/
theorem linear_interior_regime {α β γ δ τ : ℝ} (hs : 0 < β + δ) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α - γ) :
    0 ≤ (α - γ - τ) / (β + δ) ∧ (α - γ - τ) / (β + δ) ≤ (α - γ) / (β + δ) ∧
      0 ≤ deadweightLoss (fun q => α - β * q) (fun q => γ + δ * q) ((α - γ) / (β + δ))
        ((α - γ - τ) / (β + δ)) := by
  have hpos : 0 ≤ β + δ := le_of_lt hs
  have h1 : 0 ≤ α - γ - τ := by linarith
  have hq0 : 0 ≤ (α - γ - τ) / (β + δ) := div_nonneg h1 hpos
  have hle : α - γ - τ ≤ α - γ := by linarith
  have hqle : (α - γ - τ) / (β + δ) ≤ (α - γ) / (β + δ) :=
    div_le_div_of_nonneg_right hle hpos
  have hdwl : deadweightLoss (fun q => α - β * q) (fun q => γ + δ * q) ((α - γ) / (β + δ))
        ((α - γ - τ) / (β + δ)) = τ ^ 2 / (2 * (β + δ)) :=
    (deadweightLoss_linear hs).2
  rw [hdwl]
  have hsq : 0 ≤ τ ^ 2 := sq_nonneg τ
  have hden : 0 ≤ 2 * (β + δ) := mul_nonneg (by norm_num) hpos
  exact ⟨hq0, hqle, div_nonneg hsq hden⟩

end MathlibExt.Economics.DeadweightLoss
