/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Isothermal atmospheric hydrostatic structure

## i. Overview

For an isothermal ideal gas with constant gravity `g > 0`, mass-specific
gas constant `R > 0` and temperature `T > 0`, the pressure profile
`p(z) = p0 * exp(-g * z / (R * T))` with surface pressure `p0 > 0` and
height `z` upward solves the hydrostatic relation `p'(z) = -rho(z) * g`
with density `rho(z) = p(z) / (R * T)`. It satisfies `p(0) = p0`, stays
positive, is strictly decreasing in `z`, and drops to `p0 / exp 1` at one
scale height `z = R * T / g`. Each fact is a separate lemma about
`isothermalPressure` that assumes only what its proof uses. No lapse-rate
(non-isothermal) atmosphere claim is made.

## ii. Key results

- `EarthScience.isothermalPressure`: the exponential pressure profile.
- `EarthScience.hasDerivAt_isothermalPressure`: hydrostatic balance with
  `rho = p / (R * T)`.
- `EarthScience.isothermalPressure_zero`: the surface condition `p(0) = p0`.
- `EarthScience.isothermalPressure_pos`: positivity, from `p0 > 0` alone.
- `EarthScience.isothermalPressure_strictAnti`: strict decrease in `z`.
- `EarthScience.isothermalPressure_scaleHeight`: the value `p0 / exp 1` at
  one scale height.
- `EarthScience.isothermal_atmospheric_pressure`: the five facts together
  for the explicit profile, under `p0, g, R, T > 0`.

## iii. Table of contents

- A. Exponential pressure profile
- B. Combined statement

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed.,
  Cambridge University Press, 2017, ch. 2 (hydrostatic balance and the
  isothermal atmosphere).
- Exponential and derivative lemmas in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Exponential pressure profile -/

/-- Isothermal ideal-gas pressure profile `p(z) = p0 * exp(-g * z / (R * T))`,
with surface pressure `p0`, constant gravity `g`, mass-specific gas constant
`R`, temperature `T`, and height `z` measured upward. The physical regime is
`p0, g, R, T > 0`; each lemma below states the hypotheses it needs. -/
noncomputable def isothermalPressure (p0 g R T z : ℝ) : ℝ :=
  p0 * Real.exp (-g * z / (R * T))

/-- Hydrostatic balance: the isothermal profile satisfies
`p'(z) = -(p(z) / (R * T)) * g`, i.e. `p' = -rho * g` with ideal-gas density
`rho = p / (R * T)`. The derivative identity needs no sign hypotheses. -/
lemma hasDerivAt_isothermalPressure (p0 g R T z : ℝ) :
    HasDerivAt (isothermalPressure p0 g R T)
      (-(isothermalPressure p0 g R T z / (R * T)) * g) z := by
  have hinner : HasDerivAt (fun ζ : ℝ => -g * ζ / (R * T)) (-g / (R * T)) z := by
    have hbase : HasDerivAt (fun ζ : ℝ => (-g / (R * T)) * ζ) (-g / (R * T)) z := by
      simpa using (hasDerivAt_id z).const_mul (-g / (R * T))
    have hfun : (fun ζ : ℝ => -g * ζ / (R * T)) = fun ζ : ℝ => (-g / (R * T)) * ζ := by
      funext ζ
      ring
    rw [hfun]
    exact hbase
  have hmul := hinner.exp.const_mul p0
  change HasDerivAt (fun ζ : ℝ => p0 * Real.exp (-g * ζ / (R * T)))
    (-(p0 * Real.exp (-g * z / (R * T)) / (R * T)) * g) z
  convert hmul using 1
  ring

/-- Surface condition: the isothermal profile has `p(0) = p0`. -/
lemma isothermalPressure_zero (p0 g R T : ℝ) : isothermalPressure p0 g R T 0 = p0 := by
  simp [isothermalPressure]

/-- Positivity: with surface pressure `p0 > 0`, the isothermal profile is
positive at every height. -/
lemma isothermalPressure_pos {p0 : ℝ} (hp0 : 0 < p0) (g R T z : ℝ) :
    0 < isothermalPressure p0 g R T z :=
  mul_pos hp0 (Real.exp_pos _)

/-- Strict decrease: for `p0, g, R, T > 0` the isothermal pressure strictly
decreases with height. -/
lemma isothermalPressure_strictAnti {p0 g R T : ℝ} (hp0 : 0 < p0) (hg : 0 < g)
    (hR : 0 < R) (hT : 0 < T) : StrictAnti (isothermalPressure p0 g R T) := by
  intro z₁ z₂ h12
  have hneg : (-g) * z₂ < (-g) * z₁ :=
    mul_lt_mul_of_neg_left h12 (neg_lt_zero.mpr hg)
  have hdiv : -g * z₂ / (R * T) < -g * z₁ / (R * T) :=
    (div_lt_div_iff_of_pos_right (mul_pos hR hT)).mpr hneg
  exact mul_lt_mul_of_pos_left (Real.exp_strictMono hdiv) hp0

/-- One scale height: at `z = R * T / g` the isothermal pressure is
`p0 / exp 1`. -/
lemma isothermalPressure_scaleHeight (p0 : ℝ) {g R T : ℝ} (hg : g ≠ 0) (hR : R ≠ 0)
    (hT : T ≠ 0) : isothermalPressure p0 g R T (R * T / g) = p0 / Real.exp 1 := by
  have hRT : R * T ≠ 0 := mul_ne_zero hR hT
  have harg : -g * (R * T / g) / (R * T) = -1 := by
    field_simp
  rw [isothermalPressure, harg, Real.exp_neg, div_eq_mul_inv]

/-! ## B. Combined statement -/

/-- Isothermal ideal-gas atmosphere: `p(z) = p0 * exp(-g * z / (R * T))`
with `p0, g, R, T > 0` satisfies the hydrostatic relation
`p'(z) = -(p(z) / (R * T)) * g` (density `rho = p / (R * T)`), has
`p(0) = p0`, stays positive, is strictly decreasing in `z`, and drops to
`p0 / exp 1` at one scale height `z = R * T / g`. The separate facts, with
their own hypotheses, are `hasDerivAt_isothermalPressure`,
`isothermalPressure_zero`, `isothermalPressure_pos`,
`isothermalPressure_strictAnti`, and `isothermalPressure_scaleHeight`. -/
theorem isothermal_atmospheric_pressure {p0 g R T : ℝ} (hp0 : 0 < p0) (hg : 0 < g)
    (hR : 0 < R) (hT : 0 < T) :
    (∀ z : ℝ, HasDerivAt (fun ζ : ℝ => p0 * Real.exp (-g * ζ / (R * T)))
        (-(p0 * Real.exp (-g * z / (R * T)) / (R * T)) * g) z) ∧
      (p0 * Real.exp (-g * (0 : ℝ) / (R * T)) = p0) ∧
      (∀ z : ℝ, 0 < p0 * Real.exp (-g * z / (R * T))) ∧
      (∀ z₁ z₂ : ℝ, z₁ < z₂ →
        p0 * Real.exp (-g * z₂ / (R * T)) < p0 * Real.exp (-g * z₁ / (R * T))) ∧
      (p0 * Real.exp (-g * (R * T / g) / (R * T)) = p0 / Real.exp 1) :=
  ⟨fun z => hasDerivAt_isothermalPressure p0 g R T z, isothermalPressure_zero p0 g R T,
    fun z => isothermalPressure_pos hp0 g R T z,
    fun _ _ h12 => isothermalPressure_strictAnti hp0 hg hR hT h12,
    isothermalPressure_scaleHeight p0 hg.ne' hR.ne' hT.ne'⟩

end EarthScience
