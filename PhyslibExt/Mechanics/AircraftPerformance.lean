/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.IsothermalAtmosphericPressure

import Mathlib.Tactic.FieldSimp

/-!
# Aircraft performance: isothermal density on a declared altitude band

## i. Overview

In an isothermal hydrostatic layer with constant gravity, the density at height `z` above the
reference level is the mass-specific ideal-gas relation `ρ = p / (Rs * T)` applied to the
existing isothermal pressure profile `EarthScience.isothermalPressure`, with reference pressure
`ρ0 * Rs * T`. It equals `ρ0 * exp (-z / H)` with scale height `H = Rs * T / |g|`.

Model inputs: hydrostatic balance and the ideal-gas equation of state (both carried by the
pressure profile), constant absolute temperature `T > 0`, constant gravity of magnitude `g > 0`
with `z` measured upward, mass-specific gas constant `Rs > 0` and reference density `ρ0 > 0`.
The model is asserted only on a declared finite band `[z₁, z₂]` of heights: the band results
carry `z ∈ Set.Icc z₁ z₂`, and `isothermalDensity_band_bounds_fail_outside` shows that the
band bounds are false outside the band. Variable-temperature standard atmospheres and rarefied
flow are different models and are not claimed. Each result assumes only the hypotheses its
proof uses.

Units: a change of units multiplies a coordinate of dimension `M^a L^b T^c Θ^d` by
`m^a * l^b * s^c * k^d`, where `m, l, s, k > 0` count the new mass, length, time and
temperature units in one old unit (metres to kilometres: `l = 1 / 1000`). The density formula
commutes with every such change. A Celsius reading is affine, not a coordinate of a change of
units, and is never a valid `T`.

## ii. Key results

- `AircraftPerformance.isothermalDensity_eq_exp`: `ρ(z) = ρ0 * exp (-z / H)`.
- `AircraftPerformance.hasDerivAt_isothermalPressure_density`: `p'(z) = -ρ(z) * g`.
- `AircraftPerformance.isothermalDensity_band_bounds`: positive monotone bounds on a band.
- `AircraftPerformance.isothermalDensity_band_bounds_fail_outside`: no extrapolation.
- `AircraftPerformance.isothermalDensity_unitChange`, `scaleHeight_unitChange`: units.

## iii. Table of contents

- A. Scale height and density
- B. Bounds on a declared band
- C. Change of units

## iv. References

- J. D. Anderson, *Introduction to Flight*, McGraw-Hill, ch. 3 (the standard atmosphere and
  its isothermal layers, `ρ / ρ₁ = exp (-(g₀ / (R T)) (h - h₁))`).
- ISO 2533:1975, *Standard Atmosphere*: the layer from 11 km to 20 km is isothermal at
  216.65 K, with `g₀ = 9.80665 m/s²`.
-/

@[expose] public section

namespace AircraftPerformance

open EarthScience

/-! ## A. Scale height and density -/

/-- Scale height `H = Rs * T / |g|` of an isothermal layer with mass-specific gas constant `Rs`,
absolute temperature `T` and gravitational acceleration of magnitude `|g|`; it is a length.
At `g = 0` Lean's convention `x / 0 = 0` gives the meaningless value `0`. -/
noncomputable def scaleHeight (Rs T g : ℝ) : ℝ := Rs * T / |g|

/-- Density at height `z` of the isothermal layer with reference density `ρ0`: the ideal-gas
relation `ρ = p / (Rs * T)` applied to `isothermalPressure` with reference pressure
`ρ0 * Rs * T`. The physical regime is `ρ0, g, Rs, T > 0`, `z` upward, `z` in a declared band. -/
noncomputable def isothermalDensity (ρ0 g Rs T z : ℝ) : ℝ :=
  isothermalPressure (ρ0 * Rs * T) g Rs T z / (Rs * T)

/-- The density obtained from the pressure profile and the ideal-gas relation is
`ρ(z) = ρ0 * exp (-z / H)` with `H = Rs * T / |g|`. -/
lemma isothermalDensity_eq_exp {g Rs T : ℝ} (hg : 0 < g) (hRs : 0 < Rs) (hT : 0 < T)
    (ρ0 z : ℝ) :
    isothermalDensity ρ0 g Rs T z = ρ0 * Real.exp (-z / scaleHeight Rs T g) := by
  have hg' : g ≠ 0 := ne_of_gt hg
  have hRT : (Rs * T : ℝ) ≠ 0 := mul_ne_zero (ne_of_gt hRs) (ne_of_gt hT)
  have habs : |g| = g := abs_of_pos hg
  have harg : (-g * z / (Rs * T) : ℝ) = -z / scaleHeight Rs T g := by
    unfold scaleHeight
    rw [habs]
    field_simp
  unfold isothermalDensity isothermalPressure
  rw [harg]
  field_simp

/-- Hydrostatic balance in density form: the pressure profile with reference pressure
`ρ0 * Rs * T` satisfies `p'(z) = -ρ(z) * g` for `ρ = isothermalDensity ρ0 g Rs T`. -/
lemma hasDerivAt_isothermalPressure_density (ρ0 g Rs T z : ℝ) :
    HasDerivAt (isothermalPressure (ρ0 * Rs * T) g Rs T)
      (-(isothermalDensity ρ0 g Rs T z) * g) z := by
  unfold isothermalDensity
  exact hasDerivAt_isothermalPressure _ _ _ _ _

/-- The density is positive at every height when `ρ0, Rs, T > 0`. -/
lemma isothermalDensity_pos {ρ0 Rs T : ℝ} (hρ0 : 0 < ρ0) (hRs : 0 < Rs) (hT : 0 < T)
    (g z : ℝ) : 0 < isothermalDensity ρ0 g Rs T z := by
  unfold isothermalDensity
  exact div_pos (isothermalPressure_pos (mul_pos (mul_pos hρ0 hRs) hT) g Rs T z)
    (mul_pos hRs hT)

/-- The scale height is positive for `Rs, T > 0` and nonzero gravity. -/
lemma scaleHeight_pos {Rs T g : ℝ} (hRs : 0 < Rs) (hT : 0 < T) (hg : g ≠ 0) :
    0 < scaleHeight Rs T g := by
  unfold scaleHeight
  exact div_pos (mul_pos hRs hT) (abs_pos.mpr hg)

/-! ## B. Bounds on a declared band -/

/-- On a declared band `[z₁, z₂]` the density strictly decreases with height. -/
lemma isothermalDensity_strictAntiOn {ρ0 g Rs T : ℝ} (hρ0 : 0 < ρ0) (hg : 0 < g)
    (hRs : 0 < Rs) (hT : 0 < T) (z₁ z₂ : ℝ) :
    StrictAntiOn (isothermalDensity ρ0 g Rs T) (Set.Icc z₁ z₂) := by
  have hRT : (0:ℝ) < Rs * T := mul_pos hRs hT
  have hpress := isothermalPressure_strictAnti (mul_pos (mul_pos hρ0 hRs) hT) hg hRs hT
  intro a _ b _ hab
  unfold isothermalDensity
  exact (div_lt_div_iff_of_pos_right hRT).mpr (hpress hab)

/-- Engineering density bounds on a declared band: for `z ∈ [z₁, z₂]`,
`0 < ρ0 * exp (-z₂ / H) ≤ ρ(z) ≤ ρ0 * exp (-z₁ / H)`. -/
lemma isothermalDensity_band_bounds {ρ0 g Rs T z₁ z₂ z : ℝ} (hρ0 : 0 < ρ0) (hg : 0 < g)
    (hRs : 0 < Rs) (hT : 0 < T) (hz : z ∈ Set.Icc z₁ z₂) :
    0 < ρ0 * Real.exp (-z₂ / scaleHeight Rs T g) ∧
      ρ0 * Real.exp (-z₂ / scaleHeight Rs T g) ≤ isothermalDensity ρ0 g Rs T z ∧
      isothermalDensity ρ0 g Rs T z ≤ ρ0 * Real.exp (-z₁ / scaleHeight Rs T g) := by
  have hH : (0:ℝ) < scaleHeight Rs T g := scaleHeight_pos hRs hT (ne_of_gt hg)
  have hρ0' : (0:ℝ) ≤ ρ0 := le_of_lt hρ0
  obtain ⟨h1, h2⟩ := hz
  rw [isothermalDensity_eq_exp hg hRs hT]
  refine ⟨mul_pos hρ0 (Real.exp_pos _), ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hH).mpr (neg_le_neg h2))) hρ0'
  · exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hH).mpr (neg_le_neg h1))) hρ0'

/-- The band bounds do not extend beyond the band: below `z₁` the density exceeds the upper
bound `ρ0 * exp (-z₁ / H)`, and above `z₂` it falls below the lower bound
`ρ0 * exp (-z₂ / H)`. The band hypothesis of `isothermalDensity_band_bounds` cannot be
dropped. -/
lemma isothermalDensity_band_bounds_fail_outside {ρ0 g Rs T z₁ z₂ z : ℝ} (hρ0 : 0 < ρ0)
    (hg : 0 < g) (hRs : 0 < Rs) (hT : 0 < T) :
    (z < z₁ → ρ0 * Real.exp (-z₁ / scaleHeight Rs T g) < isothermalDensity ρ0 g Rs T z) ∧
      (z₂ < z → isothermalDensity ρ0 g Rs T z < ρ0 * Real.exp (-z₂ / scaleHeight Rs T g)) := by
  have hH : (0:ℝ) < scaleHeight Rs T g := scaleHeight_pos hRs hT (ne_of_gt hg)
  rw [isothermalDensity_eq_exp hg hRs hT]
  constructor
  · intro h
    exact mul_lt_mul_of_pos_left
      (Real.exp_strictMono ((div_lt_div_iff_of_pos_right hH).mpr (neg_lt_neg h))) hρ0
  · intro h
    exact mul_lt_mul_of_pos_left
      (Real.exp_strictMono ((div_lt_div_iff_of_pos_right hH).mpr (neg_lt_neg h))) hρ0

/-! ## C. Change of units

Density has dimension `M L⁻³`, gravity `L T⁻²`, the mass-specific gas constant
`L² T⁻² Θ⁻¹`, temperature `Θ` and height `L`. -/

/-- The density formula commutes with a change of units with length, time and temperature
factors `l, s, k > 0`, for every mass factor `m`: rescaled inputs give the rescaled density. -/
lemma isothermalDensity_unitChange (m : ℝ) {l s k Rs T : ℝ} (hl : 0 < l) (hs : 0 < s)
    (hk : 0 < k) (hRs : 0 < Rs) (hT : 0 < T) (ρ0 g z : ℝ) :
    isothermalDensity (m / l ^ 3 * ρ0) (l / s ^ 2 * g) (l ^ 2 / (s ^ 2 * k) * Rs) (k * T)
        (l * z) = m / l ^ 3 * isothermalDensity ρ0 g Rs T z := by
  have hl' : l ≠ 0 := ne_of_gt hl
  have hs' : s ≠ 0 := ne_of_gt hs
  have hk' : k ≠ 0 := ne_of_gt hk
  have hRs' : Rs ≠ 0 := ne_of_gt hRs
  have hT' : T ≠ 0 := ne_of_gt hT
  have hs2 : (s ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hs'
  have hsk : (s ^ 2 * k : ℝ) ≠ 0 := mul_ne_zero hs2 hk'
  have hl3 : (l ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 hl'
  have hRT : (Rs * T : ℝ) ≠ 0 := mul_ne_zero hRs' hT'
  have hRs'' : (l ^ 2 / (s ^ 2 * k) * Rs : ℝ) ≠ 0 :=
    mul_ne_zero (div_ne_zero (pow_ne_zero 2 hl') hsk) hRs'
  have hkT : (k * T : ℝ) ≠ 0 := mul_ne_zero hk' hT'
  have hD' : ((l ^ 2 / (s ^ 2 * k) * Rs) * (k * T) : ℝ) ≠ 0 := mul_ne_zero hRs'' hkT
  have hE : (-(l / s ^ 2 * g) * (l * z) / ((l ^ 2 / (s ^ 2 * k) * Rs) * (k * T)) : ℝ)
      = -g * z / (Rs * T) := by
    field_simp
  unfold isothermalDensity isothermalPressure
  rw [hE]
  field_simp

/-- The scale height transforms as a length under a change of units. -/
lemma scaleHeight_unitChange {l s k : ℝ} (hl : 0 < l) (hs : 0 < s) (hk : 0 < k)
    (Rs T g : ℝ) :
    scaleHeight (l ^ 2 / (s ^ 2 * k) * Rs) (k * T) (l / s ^ 2 * g) = l * scaleHeight Rs T g := by
  have hl' : l ≠ 0 := ne_of_gt hl
  have hs' : s ≠ 0 := ne_of_gt hs
  have hk' : k ≠ 0 := ne_of_gt hk
  have hs2 : (s ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hs'
  have hsk : (s ^ 2 * k : ℝ) ≠ 0 := mul_ne_zero hs2 hk'
  have hls : (0:ℝ) < l / s ^ 2 := div_pos hl (pow_pos hs 2)
  unfold scaleHeight
  by_cases hg0 : g = 0
  · subst hg0
    simp
  · have habs : |g| ≠ 0 := abs_ne_zero.mpr hg0
    have hls' : (l / s ^ 2 : ℝ) ≠ 0 := ne_of_gt hls
    have hD : ((l / s ^ 2) * |g| : ℝ) ≠ 0 := mul_ne_zero hls' habs
    rw [abs_mul, abs_of_pos hls]
    field_simp

end AircraftPerformance
