/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Static stability and parcel buoyancy

For a dry locally linear potential-temperature profile
`theta(z) = theta0 + a * z` (`z` upward), a parcel displaced by `zeta`
keeps `theta0` while the ambient value at `zeta` is `theta0 + a * zeta`.
The buoyancy acceleration is `-(g * a / theta0) * zeta`, and the squared
Brunt-Vaisala frequency is `N^2 = g * a / theta0`: `a > 0` stable,
`a = 0` neutral, `a < 0` unstable. This is a local dry-parcel model;
moist CAPE and entrainment are not inferred.

## i. Overview

The buoyancy acceleration is the potential-temperature contrast divided
by the reference value, times `g`. The oscillator theorem converts a
buoyancy-law derivative hypothesis for the parcel velocity into
`zeta'' + N^2 * zeta = 0`, in the form `v' = -(g * a / theta0) * zeta`.

## ii. Key results

- `EarthScience.potential_temp_buoyancy_accel`: buoyancy acceleration formula.
- `EarthScience.brunt_vaisala_sq_sign`: sign classification of `N^2`.
- `EarthScience.static_stability_oscillator`: velocity derivative in oscillator form.

## iii. Table of contents

- A. Buoyancy acceleration and stability signs
- B. Parcel oscillator

## iv. References

- `div_pos_iff` / `div_neg_iff` / `div_eq_zero_iff` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Buoyancy acceleration of a dry parcel displaced by `zeta` in a locally
linear potential-temperature profile `theta(z) = theta0 + a * z`: the
parcel keeps `theta0`, the ambient value at `zeta` is `theta0 + a * zeta`,
so the acceleration is `-(g * a / theta0) * zeta`. -/
theorem potential_temp_buoyancy_accel {g a theta0 zeta : ℝ} (hth : theta0 ≠ 0) :
    g * (theta0 - (theta0 + a * zeta)) / theta0 = -(g * a / theta0) * zeta := by
  field_simp
  ring

/-- Sign classification of `N^2 = g * a / theta0` for `g, theta0 > 0`:
stable (`a > 0`), neutral (`a = 0`), unstable (`a < 0`). -/
theorem brunt_vaisala_sq_sign {g a theta0 : ℝ} (hg : 0 < g) (hth : 0 < theta0) :
    (0 < g * a / theta0 ↔ 0 < a) ∧ (g * a / theta0 = 0 ↔ a = 0) ∧
      (g * a / theta0 < 0 ↔ a < 0) := by
  have hg_ne : g ≠ 0 := ne_of_gt hg
  have hth_ne : theta0 ≠ 0 := ne_of_gt hth
  have hpos : 0 < g * a / theta0 ↔ 0 < a := by
    rw [div_pos_iff]
    constructor
    · rintro (⟨hga, _⟩ | ⟨_, hneg⟩)
      · exact (mul_pos_iff_of_pos_left hg).mp hga
      · exact absurd hneg (not_lt_of_gt hth)
    · intro ha
      exact Or.inl ⟨(mul_pos_iff_of_pos_left hg).mpr ha, hth⟩
  have hzero : g * a / theta0 = 0 ↔ a = 0 := by
    rw [div_eq_zero_iff, mul_eq_zero]
    constructor
    · rintro ((hg0 | ha0) | hth0)
      · exact absurd hg0 hg_ne
      · exact ha0
      · exact absurd hth0 hth_ne
    · intro ha
      exact Or.inl (Or.inr ha)
  have hneg : g * a / theta0 < 0 ↔ a < 0 := by
    rw [div_neg_iff]
    constructor
    · rintro (⟨_, hneg⟩ | ⟨hga, _⟩)
      · exact absurd hneg (not_lt_of_gt hth)
      · rw [mul_neg_iff] at hga
        rcases hga with ⟨_, ha⟩ | ⟨hgneg, _⟩
        · exact ha
        · exact absurd hgneg (not_lt_of_gt hg)
    · intro ha
      exact Or.inr ⟨by rw [mul_neg_iff]; exact Or.inl ⟨hg, ha⟩, hth⟩
  exact ⟨hpos, hzero, hneg⟩

/-- If the parcel velocity `v` has derivative equal to the buoyancy
acceleration from the potential-temperature contrast, then it satisfies
`zeta'' + N^2 * zeta = 0` with `N^2 = g * a / theta0`, in the form
`v' = -(g * a / theta0) * zeta`. -/
theorem static_stability_oscillator {zeta v : ℝ → ℝ} {t : ℝ} {g a theta0 : ℝ}
    (hth : theta0 ≠ 0)
    (hbuoy : HasDerivAt v (g * (theta0 - (theta0 + a * zeta t)) / theta0) t) :
    HasDerivAt v (-(g * a / theta0) * zeta t) t := by
  have hEq : g * (theta0 - (theta0 + a * zeta t)) / theta0 =
      -(g * a / theta0) * zeta t :=
    potential_temp_buoyancy_accel hth
  exact hbuoy.congr_deriv hEq

end EarthScience
