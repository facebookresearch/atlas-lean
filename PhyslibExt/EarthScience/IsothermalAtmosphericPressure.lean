/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Isothermal atmospheric hydrostatic structure

## i. Overview

For an isothermal ideal gas with constant gravity `g > 0`, mass-specific
gas constant `R > 0` and temperature `T > 0`, the pressure profile
`p(z) = p0 * exp(-g * z / (R * T))` with surface pressure `p0 > 0` and
height `z` upward solves the hydrostatic relation `p'(z) = -rho(z) * g`
with density `rho(z) = p(z) / (R * T)`. It satisfies `p(0) = p0`, stays
positive, is strictly decreasing in `z`, and drops to `p0 / exp 1` at one
scale height `z = R * T / g`. No lapse-rate (non-isothermal) atmosphere
claim is made.

## ii. Key results

- `EarthScience.isothermal_atmospheric_pressure`: the exponential profile
  above satisfies hydrostatic balance with `rho = p / (R * T)`, the surface
  condition, positivity, strict decrease, and the one-scale-height value.

## iii. Table of contents

- A. Exponential pressure profile

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed.,
  Cambridge University Press, 2017, ch. 2 (hydrostatic balance and the
  isothermal atmosphere).
- Exponential and derivative lemmas in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Exponential pressure profile -/

/-- Isothermal ideal-gas atmosphere: `p(z) = p0 * exp(-g * z / (R * T))`
with `p0, g, R, T > 0` satisfies the hydrostatic relation
`p'(z) = -(p(z) / (R * T)) * g` (density `rho = p / (R * T)`), has
`p(0) = p0`, stays positive, is strictly decreasing in `z`, and drops to
`p0 / exp 1` at one scale height `z = R * T / g`. -/
theorem isothermal_atmospheric_pressure {p0 g R T : ℝ} (hp0 : 0 < p0) (hg : 0 < g)
    (hR : 0 < R) (hT : 0 < T) :
    (∀ z : ℝ, HasDerivAt (fun ζ : ℝ => p0 * Real.exp (-g * ζ / (R * T)))
        (-(p0 * Real.exp (-g * z / (R * T)) / (R * T)) * g) z) ∧
      (p0 * Real.exp (-g * (0 : ℝ) / (R * T)) = p0) ∧
      (∀ z : ℝ, 0 < p0 * Real.exp (-g * z / (R * T))) ∧
      (∀ z₁ z₂ : ℝ, z₁ < z₂ →
        p0 * Real.exp (-g * z₂ / (R * T)) < p0 * Real.exp (-g * z₁ / (R * T))) ∧
      (p0 * Real.exp (-g * (R * T / g) / (R * T)) = p0 / Real.exp 1) := by
  have hRTpos : 0 < R * T := mul_pos hR hT
  have hRTne : R * T ≠ 0 := ne_of_gt hRTpos
  have hgne : g ≠ 0 := ne_of_gt hg
  refine ⟨?hderiv, ?h0, ?hpos, ?hdec, ?hscale⟩
  · intro z
    have hinner : HasDerivAt (fun ζ : ℝ => -g * ζ / (R * T)) (-g / (R * T)) z := by
      have hbase : HasDerivAt (fun ζ : ℝ => (-g / (R * T)) * ζ) (-g / (R * T)) z := by
        simpa using (hasDerivAt_id z).const_mul (-g / (R * T))
      have hfun : (fun ζ : ℝ => -g * ζ / (R * T)) = fun ζ : ℝ => (-g / (R * T)) * ζ := by
        funext ζ
        ring
      rw [hfun]
      exact hbase
    have hexp : HasDerivAt (fun ζ : ℝ => Real.exp (-g * ζ / (R * T)))
        (Real.exp (-g * z / (R * T)) * (-g / (R * T))) z :=
      hinner.exp
    have hmul := hexp.const_mul p0
    convert hmul using 1
    field_simp
  · have harg : -g * (0 : ℝ) / (R * T) = 0 := by simp
    rw [harg, Real.exp_zero, mul_one]
  · intro z
    exact mul_pos hp0 (Real.exp_pos _)
  · intro z₁ z₂ h12
    have hneg : (-g) * z₂ < (-g) * z₁ :=
      mul_lt_mul_of_neg_left h12 (neg_lt_zero.mpr hg)
    have hdiv : -g * z₂ / (R * T) < -g * z₁ / (R * T) :=
      (div_lt_div_iff_of_pos_right hRTpos).mpr hneg
    have hexp : Real.exp (-g * z₂ / (R * T)) < Real.exp (-g * z₁ / (R * T)) :=
      Real.exp_strictMono hdiv
    exact mul_lt_mul_of_pos_left hexp hp0
  · have harg : -g * (R * T / g) / (R * T) = -1 := by
      field_simp
    rw [harg, Real.exp_neg, div_eq_mul_inv]

end EarthScience
