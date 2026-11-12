/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Capstone: stratified rotating column

## i. Overview

Same z-up frame throughout. Atmosphere and ocean use explicitly
different equations of state; this is an interface reuse test, not a
unification of incompatible constitutive laws. Atmosphere:
Brunt-Väisälä `N² = (g / θ) * dθ / dz` with `g > 0`, reference
potential temperature `θ > 0`, and dry-potential-temperature gradient
`dθ / dz > 0` gives `N² > 0`. Ocean: Boussinesq
`N² = -(g / ρ₀) * dρ / dz` with `g > 0`, reference density `ρ₀ > 0`,
and `dρ / dz < 0` gives `N² > 0`. Geostrophic wind
`v = -(1 / (ρ * f)) * dp / dx` with stated axes. This capstone is
proved self-contained from Mathlib primitives; it does not depend on
any sibling development.

## ii. Key results

- `EarthScience.bruntVaisala_atmosphere_pos`: atmospheric `N² > 0`.
- `EarthScience.bruntVaisala_ocean_pos`: oceanic `N² > 0`.
- `EarthScience.geostrophic_wind_value`: `ρ = 1025, f = 10⁻⁴,
  dp / dx = 0.01` gives `v = -4 / 41 m/s ≈ -0.09756 m/s`.
- `EarthScience.geostrophic_rejects_equator`: `f = 0` makes the
  denominator `ρ * f = 0`.
- `EarthScience.geostrophic_sign_cases`: north `f > 0` gives `v < 0`,
  south `f < 0` gives `v > 0`, for `dp / dx > 0`.

## iii. Table of contents

- A. Brunt-Väisälä positivity, atmosphere and ocean
- B. Geostrophic inversion

## iv. References

- `div_pos`, `mul_pos`, `one_div_pos`, `one_div_neg` in Mathlib.

## A. Brunt-Väisälä positivity, atmosphere and ocean
-/

@[expose] public section

namespace EarthScience


/-- Capstone (stratified rotating column, atmosphere): in the same
z-up frame, Brunt-Väisälä frequency squared
`N² = (g / θ) * dθ / dz` is positive when `g > 0`, `θ > 0` and
`dθ / dz > 0` (positive dry-potential-temperature gradient). -/
theorem bruntVaisala_atmosphere_pos {g θ dθ : ℝ} (hg : 0 < g) (hθ : 0 < θ)
    (hdθ : 0 < dθ) : 0 < (g / θ) * dθ := by
  exact mul_pos (div_pos hg hθ) hdθ

/-- Ocean: Boussinesq `N² = -(g / ρ₀) * dρ / dz` is positive when
`g > 0`, `ρ₀ > 0` and `dρ / dz < 0` (density decreasing with height). -/
theorem bruntVaisala_ocean_pos {g ρ₀ dρ : ℝ} (hg : 0 < g) (hρ : 0 < ρ₀)
    (hdρ : dρ < 0) : 0 < -(g / ρ₀) * dρ := by
  have hdiv : 0 < g / ρ₀ := div_pos hg hρ
  have hneg : -(g / ρ₀) < 0 := by linarith
  exact mul_pos_of_neg_of_neg hneg hdρ

/-! ## B. Geostrophic inversion -/

/-- Geostrophic inversion, concrete case: for `ρ = 1025 kg/m³`,
`f = 10⁻⁴ s⁻¹`, `dp / dx = 0.01 Pa/m`, the geostrophic wind
`v = -(1 / (ρ * f)) * dp / dx` is `-4 / 41 m/s ≈ -0.09756 m/s`. -/
theorem geostrophic_wind_value :
    -(1 / (1025 * (1 / 10000 : ℝ))) * (1 / 100) = -4 / 41 := by
  norm_num

/-- Geostrophic inversion rejects `f = 0`: the denominator `ρ * f`
is `0` when `f = 0`, so the inversion formula has no finite value. -/
theorem geostrophic_rejects_equator {ρ : ℝ} : ρ * (0 : ℝ) = 0 := by
  exact mul_zero _

/-- Sign cases in the same z-up frame: for `dp / dx > 0`, northern
`f > 0` gives `v < 0` and southern `f < 0` gives `v > 0`. -/
theorem geostrophic_sign_cases {ρ f dpdx : ℝ} (hρ : 0 < ρ) (hdp : 0 < dpdx) :
    (0 < f → -(1 / (ρ * f)) * dpdx < 0) ∧
      (f < 0 → 0 < -(1 / (ρ * f)) * dpdx) := by
  constructor
  · intro hf
    have hrf : 0 < ρ * f := mul_pos hρ hf
    have h1 : 0 < 1 / (ρ * f) := one_div_pos.mpr hrf
    have hneg : -(1 / (ρ * f)) < 0 := by linarith
    exact mul_neg_of_neg_of_pos hneg hdp
  · intro hf
    have hrf : ρ * f < 0 := mul_neg_of_pos_of_neg hρ hf
    have h1 : 1 / (ρ * f) < 0 := one_div_neg.mpr hrf
    have hpos : 0 < -(1 / (ρ * f)) := by linarith
    exact mul_pos hpos hdp


end EarthScience
