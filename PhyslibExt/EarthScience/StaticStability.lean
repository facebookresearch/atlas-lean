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

This is the dry parcel method (Holton and Hakim, §2.7.3; Wallace and
Hobbs, §3.6) with its approximations made explicit:

- the parcel moves dry-adiabatically, so it keeps its potential
  temperature `theta0`, and its pressure adjusts at once to the ambient
  pressure;
- the ambient profile is linearized about the parcel's equilibrium level,
  `theta(z) = theta0 + a * z` with `a = dtheta/dz` there;
- the buoyancy acceleration `g * (theta_parcel - theta_ambient) / theta0`
  divides by the reference value `theta0` rather than by the ambient value
  at the displaced level, which is accurate for small displacements
  (`|a * zeta|` much smaller than `theta0`).

Under these approximations `N^2 = g * a / theta0` is the textbook
`N^2 = g * d(ln theta)/dz` at the equilibrium level. With the kinematic
relation `zeta' = v` and the buoyancy law for `v'`, the displacement obeys
the oscillator equation `zeta'' + N^2 * zeta = 0`. Without the kinematic
relation, `buoyancy_deriv_rewrite` only rewrites the value of `v'`.

## ii. Key results

- `EarthScience.potential_temp_buoyancy_accel`: buoyancy acceleration formula.
- `EarthScience.brunt_vaisala_sq_sign`: sign classification of `N^2`.
- `EarthScience.buoyancy_deriv_rewrite`: the buoyancy-law derivative of `v`
  rewritten as `-(g * a / theta0) * zeta` (an algebraic rewrite only).
- `EarthScience.static_stability_oscillator`: `zeta' = v` and the buoyancy
  law give `zeta'' = -N^2 * zeta`.
- `EarthScience.static_stability_oscillator_eq`: the same equation as
  `zeta'' + N^2 * zeta = 0`.

## iii. Table of contents

- A. Buoyancy acceleration and stability signs
- B. Parcel oscillator

## iv. References

- James R. Holton and Gregory J. Hakim, *An Introduction to Dynamic
  Meteorology*, 5th ed., Academic Press, 2013, §2.7.3 (static stability:
  parcel method, buoyancy oscillation `d²(δz)/dt² = -N² δz`,
  `N² = g d(ln θ)/dz`).
- John M. Wallace and Peter V. Hobbs, *Atmospheric Science: An Introductory
  Survey*, 2nd ed., Academic Press, 2006, §3.6 (static stability and the
  Brunt-Vaisala frequency of unsaturated air).
- `div_pos_iff` / `div_neg_iff` / `div_eq_zero_iff` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Buoyancy acceleration of a dry parcel displaced by `zeta` in a locally
linear potential-temperature profile `theta(z) = theta0 + a * z`: the
parcel keeps `theta0`, the ambient value at `zeta` is `theta0 + a * zeta`,
so the acceleration is `-(g * a / theta0) * zeta` (Holton and Hakim,
§2.7.3, under the approximations listed in the module docstring). -/
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

/-- Algebraic rewrite of the buoyancy law: if `v` has derivative
`g * (theta0 - (theta0 + a * zeta t)) / theta0` at `t`, it has derivative
`-(g * a / theta0) * zeta t`. This only rewrites the derivative value. It
does not relate `v` to the derivative of `zeta`, so it is not an
oscillator equation; `static_stability_oscillator` adds that relation. -/
lemma buoyancy_deriv_rewrite {zeta v : ℝ → ℝ} {t : ℝ} {g a theta0 : ℝ}
    (hth : theta0 ≠ 0)
    (hbuoy : HasDerivAt v (g * (theta0 - (theta0 + a * zeta t)) / theta0) t) :
    HasDerivAt v (-(g * a / theta0) * zeta t) t := by
  have hEq : g * (theta0 - (theta0 + a * zeta t)) / theta0 =
      -(g * a / theta0) * zeta t :=
    potential_temp_buoyancy_accel hth
  exact hbuoy.congr_deriv hEq

/-- **Static-stability oscillator.** If the parcel velocity is the time
derivative of its displacement, `zeta' = v`, and `v` obeys the buoyancy
law at `t`, then `zeta'' (t) = -N^2 * zeta t` with `N^2 = g * a / theta0`
(Holton and Hakim, §2.7.3). If the buoyancy law holds at every time, this
is the oscillator equation `zeta'' + N^2 * zeta = 0`. -/
theorem static_stability_oscillator {zeta v : ℝ → ℝ} {t : ℝ} {g a theta0 : ℝ}
    (hth : theta0 ≠ 0) (hvel : ∀ s, HasDerivAt zeta (v s) s)
    (hbuoy : HasDerivAt v (g * (theta0 - (theta0 + a * zeta t)) / theta0) t) :
    HasDerivAt (deriv zeta) (-(g * a / theta0) * zeta t) t := by
  have hv : deriv zeta = v := funext fun s => (hvel s).deriv
  rw [hv]
  exact buoyancy_deriv_rewrite hth hbuoy

/-- The static-stability oscillator equation `zeta'' + N^2 * zeta = 0` at
`t`, with `N^2 = g * a / theta0`, under the hypotheses of
`static_stability_oscillator`. -/
theorem static_stability_oscillator_eq {zeta v : ℝ → ℝ} {t : ℝ} {g a theta0 : ℝ}
    (hth : theta0 ≠ 0) (hvel : ∀ s, HasDerivAt zeta (v s) s)
    (hbuoy : HasDerivAt v (g * (theta0 - (theta0 + a * zeta t)) / theta0) t) :
    deriv (deriv zeta) t + g * a / theta0 * zeta t = 0 := by
  rw [(static_stability_oscillator hth hvel hbuoy).deriv]
  ring

end EarthScience
