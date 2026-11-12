/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

## Main results

* `MathlibExt.Economics.Finance.RetentionValue.retentionGrowth`: dividend growth `b * ROE`.
* `MathlibExt.Economics.Finance.RetentionValue.retentionPrice`: Gordon price with reinvestment.
* `MathlibExt.Economics.Finance.RetentionValue.noGrowthPrice`: no-growth price `E₁ / r`.
* `MathlibExt.Economics.Finance.RetentionValue.retentionPrice_eq_gordonForm`: `retentionPrice`
  is the Gordon formula with the reinvestment-model dividend and growth substituted in.
* `MathlibExt.Economics.Finance.RetentionValue.retentionCreatesValue_iff`: value
  creation iff `ROE > r`.

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
`D₁ = E₁ * (1 - b)` and `g = b * ROE` (source clause: "`P = E₁(1-b) / (r - b*ROE)`"). -/
noncomputable def retentionPrice (E₁ b ROE r : ℝ) : ℝ :=
  E₁ * (1 - b) / (r - b * ROE)

/-- No-retention (all earnings paid out) equity price `E₁ / r` (source clause: "no-growth
value"). -/
noncomputable def noGrowthPrice (E₁ r : ℝ) : ℝ :=
  E₁ / r

/-- `retentionPrice` is exactly the Gordon formula with the reinvestment-model dividend
and growth substituted in. -/
theorem retentionPrice_eq_gordonForm {E₁ b ROE r : ℝ} :
    retentionPrice E₁ b ROE r = E₁ * (1 - b) / (r - retentionGrowth b ROE) := by
  rfl

/-- **Retained earnings create value iff `ROE > r`.** With positive earnings, a positive
retention share, a positive required return, and growth below the required return
(`b * ROE < r`, so the Gordon denominator is positive), the retention price exceeds the
no-growth price exactly when the reinvestment return exceeds the required return. -/
theorem retentionCreatesValue_iff {E₁ b ROE r : ℝ} (hE : 0 < E₁) (hb₀ : 0 < b)
    (hr : 0 < r) (hg : b * ROE < r) :
    retentionPrice E₁ b ROE r > noGrowthPrice E₁ r ↔ ROE > r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hden : 0 < r - b * ROE := by linarith
  have hden0 : r - b * ROE ≠ 0 := ne_of_gt hden
  have hY0 : r * (r - b * ROE) ≠ 0 := mul_ne_zero hr0 hden0
  have hEb : 0 < E₁ * b := mul_pos hE hb₀
  have hY : 0 < r * (r - b * ROE) := mul_pos hr hden
  have hkey : retentionPrice E₁ b ROE r - noGrowthPrice E₁ r
      = E₁ * b * (ROE - r) / (r * (r - b * ROE)) := by
    simp only [retentionPrice, noGrowthPrice]
    field_simp
    ring
  constructor
  · intro h
    have hpos : 0 < retentionPrice E₁ b ROE r - noGrowthPrice E₁ r := sub_pos.mpr h
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
