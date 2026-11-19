/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.GrowingPerpetuity
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Retained earnings and the value of growth

In the constant-return reinvestment model (next-year earnings `E₁`, retention share
`b`, reinvestment return `ROE`, required return `r`), retained earnings grow dividends
at `g = b * ROE`, so Gordon gives the price `E₁ * (1 - b) / (r - b * ROE)`. That
price exceeds the no-growth price `E₁ / r` exactly when `ROE > r`.

Domain note: the retained-earnings interpretation needs nonnegative earnings `E₁ ≥ 0`
and a retention share `0 ≤ b ≤ 1`, so that the dividend `E₁ * (1 - b)` is nonnegative;
the retention share alone does not suffice (`E₁ = -1`, `b = 1 / 2` gives the dividend
`-1 / 2`). The declarations below do not assume `b ≤ 1`, and only the comparison theorem
assumes `E₁ > 0`: they are algebraic extensions that also cover `b > 1` and negative
earnings. For positive earnings and `b > 1` the "dividend" is negative and the formula
values a negative-payment stream rather than equity (e.g. `E₁ = 1`, `b = 2`, `ROE = 0`,
`r = 1` gives `retentionPrice = -1`).

## Main results

* `MathlibExt.Economics.Finance.RetentionValue.retentionGrowth`: dividend growth `b * ROE`.
* `MathlibExt.Economics.Finance.RetentionValue.retentionPrice`: Gordon price with reinvestment
  (an equity price only for `E₁ ≥ 0` and `0 ≤ b ≤ 1`).
* `MathlibExt.Economics.Finance.RetentionValue.noGrowthPrice`: no-growth price `E₁ / r`.
* `MathlibExt.Economics.Finance.RetentionValue.retentionPrice_eq_gordonForm`: `retentionPrice`
  is the Gordon formula with the reinvestment-model dividend and growth substituted in
  (an algebraic identity; the price interpretation needs the next bridge).
* `MathlibExt.Economics.Finance.RetentionValue.retentionPrice_eq_growingPerpetuity`:
  under the convergence hypotheses of `growingPerpetuity_eq`, `retentionPrice` is the
  value of the corresponding growing perpetuity, so the rational expression is an
  equity price only when the discounted cash flows converge and the dividend
  `E₁ * (1 - b)` is nonnegative (e.g. `E₁ ≥ 0` and `b ≤ 1`).
* `MathlibExt.Economics.Finance.RetentionValue.retentionPrice_gt_noGrowthPrice_iff`: the
  retention price exceeds the no-growth price iff `ROE > r`, for positive earnings
  `E₁ > 0`, under the same convergence hypotheses, for every `b > 0` (an algebraic
  extension); on the retention-share domain `b ≤ 1` this says retained earnings create
  value iff `ROE > r`.

## References

OpenStax, *Principles of Finance* (stock valuation, growth opportunities / PVGO).
Atlas roadmap target FI14.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.RetentionValue


/-- Dividend growth rate in the constant-return reinvestment model: retained share `b`
times reinvestment return `ROE` (source clause: "`g = b * ROE`"). -/
noncomputable def retentionGrowth (b ROE : ℝ) : ℝ :=
  b * ROE

/-- Equity price under the constant-return reinvestment model: Gordon's formula with
`D₁ = E₁ * (1 - b)` and `g = b * ROE` (source clause: "`P = E₁(1-b) / (r - b*ROE)`").
It is an equity price only for nonnegative earnings `E₁ ≥ 0` and a retention share
`0 ≤ b ≤ 1`, where the dividend is nonnegative; the retention share alone does not
suffice (`E₁ = -1`, `b = 1 / 2` gives the dividend `-1 / 2`). The formula is defined for
every `E₁` and `b` (an algebraic extension). -/
noncomputable def retentionPrice (E₁ b ROE r : ℝ) : ℝ :=
  E₁ * (1 - b) / (r - b * ROE)

/-- No-retention (all earnings paid out) equity price `E₁ / r` (source clause: "no-growth
value"). -/
noncomputable def noGrowthPrice (E₁ r : ℝ) : ℝ :=
  E₁ / r

/-- `retentionPrice` is exactly the Gordon formula with the reinvestment-model dividend
and growth substituted in. This is an algebraic identity; on its own it does not say
the discounted cash flows converge, so the price interpretation comes from
`retentionPrice_eq_growingPerpetuity` below. -/
theorem retentionPrice_eq_gordonForm {E₁ b ROE r : ℝ} :
    retentionPrice E₁ b ROE r = E₁ * (1 - b) / (r - retentionGrowth b ROE) := by
  rfl

/-- `retentionPrice` is the value of the growing perpetuity that pays the
reinvestment-model dividend `E₁ * (1 - b)` growing at `retentionGrowth b ROE`, under the
convergence hypotheses of `growingPerpetuity_eq`. In particular, the rational
expression is an equity price only when `0 ≤ (1 + b * ROE) / (1 + r)`; without this,
e.g. `b = 1 / 2`, `ROE = -8`, `r = 1` gives ratio `-3 / 2` and the discounted flows
diverge even though the rational expression is finite. It is also an equity price only
when the payments `E₁ * (1 - b)` are nonnegative, e.g. for nonnegative earnings `E₁ ≥ 0`
and a retention share `b ≤ 1`: the identity holds for every `E₁` and `b`, but the
payments are negative for positive earnings and `b > 1`, and for negative earnings and
`b < 1` (an algebraic extension, not an equity value). -/
theorem retentionPrice_eq_growingPerpetuity {E₁ b ROE r : ℝ} (hr : 0 < 1 + r)
    (hx₀ : 0 ≤ (1 + retentionGrowth b ROE) / (1 + r))
    (hx₁ : (1 + retentionGrowth b ROE) / (1 + r) < 1) :
    retentionPrice E₁ b ROE r
      = growingPerpetuity (E₁ * (1 - b)) r (retentionGrowth b ROE) :=
  (growingPerpetuity_eq (E₁ * (1 - b)) r (retentionGrowth b ROE) hr hx₀ hx₁).symm

/-- **The retention price exceeds the no-growth price iff `ROE > r`** (an algebraic
extension of value creation by retained earnings). With positive earnings, a positive
retention parameter `b`, a positive required return, growth below the required return
(`b * ROE < r`, so the Gordon denominator is positive), and the convergence
hypothesis `0 ≤ (1 + b * ROE) / (1 + r)` (so the retention price is the value of a
convergent growing perpetuity, via `retentionPrice_eq_growingPerpetuity`), the
retention price exceeds the no-growth price exactly when the reinvestment return
exceeds the required return. The statement does not assume `b ≤ 1`, so it extends
past the retention-share domain: for `b > 1` the "dividend" `E₁ * (1 - b)` is negative
and the comparison is between formulas, not equity values. On the retention-share
domain `0 < b ≤ 1` it says that retained earnings create value iff `ROE > r`. -/
theorem retentionPrice_gt_noGrowthPrice_iff {E₁ b ROE r : ℝ} (hE : 0 < E₁) (hb₀ : 0 < b)
    (hr : 0 < r) (hg : b * ROE < r)
    (hx₀ : 0 ≤ (1 + retentionGrowth b ROE) / (1 + r)) :
    retentionPrice E₁ b ROE r > noGrowthPrice E₁ r ↔ ROE > r := by
  have hr1 : 0 < 1 + r := by linarith
  have hx₁ : (1 + retentionGrowth b ROE) / (1 + r) < 1 := by
    have hgrow : retentionGrowth b ROE = b * ROE := rfl
    rw [div_lt_one hr1, hgrow]
    linarith
  -- The price in the statement is the value of a convergent growing perpetuity;
  -- rewrite it to the Gordon rational expression through that bridge.
  have hbridge : retentionPrice E₁ b ROE r
      = growingPerpetuity (E₁ * (1 - b)) r (retentionGrowth b ROE) :=
    retentionPrice_eq_growingPerpetuity hr1 hx₀ hx₁
  have hperpetuity : growingPerpetuity (E₁ * (1 - b)) r (retentionGrowth b ROE)
      = E₁ * (1 - b) / (r - retentionGrowth b ROE) :=
    growingPerpetuity_eq _ _ _ hr1 hx₀ hx₁
  rw [hbridge, hperpetuity]
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hden : 0 < r - b * ROE := by linarith
  have hden0 : r - b * ROE ≠ 0 := ne_of_gt hden
  have hY0 : r * (r - b * ROE) ≠ 0 := mul_ne_zero hr0 hden0
  have hEb : 0 < E₁ * b := mul_pos hE hb₀
  have hY : 0 < r * (r - b * ROE) := mul_pos hr hden
  have hkey : E₁ * (1 - b) / (r - retentionGrowth b ROE) - noGrowthPrice E₁ r
      = E₁ * b * (ROE - r) / (r * (r - b * ROE)) := by
    simp only [noGrowthPrice, retentionGrowth]
    field_simp
    ring
  constructor
  · intro h
    have hpos : 0 < E₁ * (1 - b) / (r - retentionGrowth b ROE) - noGrowthPrice E₁ r :=
      sub_pos.mpr h
    rw [hkey] at hpos
    have hnum : 0 < E₁ * b * (ROE - r) := by
      rcases div_pos_iff.mp hpos with ⟨h, _⟩ | ⟨_, hcon⟩
      · exact h
      · linarith
    have hsub : 0 < ROE - r := by
      by_contra hc
      push Not at hc
      have hle : E₁ * b * (ROE - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hEb.le hc
      linarith
    exact sub_pos.mp hsub
  · intro h
    have hsub : 0 < ROE - r := sub_pos.mpr h
    have hnum : 0 < E₁ * b * (ROE - r) := mul_pos hEb hsub
    have hfrac : 0 < E₁ * b * (ROE - r) / (r * (r - b * ROE)) := div_pos hnum hY
    rw [← hkey] at hfrac
    exact sub_pos.mp hfrac


end MathlibExt.Economics.Finance.RetentionValue
