/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Pointwise buoyancy and Boussinesq parcel models

For an incompressible Boussinesq parcel displaced by `zeta` in a
background density profile `rho(z) = rho0 - beta * z` (`z` upward), the
parcel keeps its density `rho0` while the ambient density at `zeta` is
`rho0 - beta * zeta`. The buoyancy acceleration is therefore
`-(g * beta / rho0) * zeta`, and the squared Brunt-Vaisala frequency is
`N^2 = g * beta / rho0`. This is a small-displacement, incompressible
model: it is not in-situ compressible seawater without an adiabatic
correction.

## i. Overview

The buoyancy acceleration is the density contrast divided by the
reference density, times `-g`. The oscillator theorem takes the parcel
velocity `v` with `zeta' = v` near `t` and the buoyancy law for `v'` at
`t`, and concludes `zeta'' t = -(g * beta / rho0) * zeta t`, where
`zeta''` is the derivative of `deriv zeta`.

## ii. Key results

- `EarthScience.boussinesq_buoyancy_accel`: buoyancy acceleration formula.
- `EarthScience.brunt_vaisala_sq_pos`: `N^2 > 0` for stable stratification.
- `EarthScience.boussinesq_parcel_oscillator`: the displacement satisfies
  `zeta'' = -(g * beta / rho0) * zeta`.

## iii. Table of contents

- A. Buoyancy acceleration and Brunt-Vaisala frequency
- B. Parcel oscillator

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics: Fundamentals and
  Large-Scale Circulation*, 2nd ed., Cambridge University Press (2017),
  Chapter 2: the Boussinesq approximation, and static stability by the
  parcel method, with buoyancy frequency `N^2 = -(g / rho0) * d rho / dz`
  for `z` upward.
- B. Cushman-Roisin and J.-M. Beckers, *Introduction to Geophysical Fluid
  Dynamics: Physical and Numerical Aspects*, 2nd ed., Academic Press
  (2011), Chapter 11: a vertically displaced parcel in a stratified fluid
  oscillates with `N^2 = -(g / rho0) * d rho / dz`.
- `div_pos` / `mul_pos` in Mathlib (positivity of division/products).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Buoyancy acceleration and Brunt-Vaisala frequency -/

/-- Buoyancy acceleration of a Boussinesq parcel displaced by `zeta` in
background `rho(z) = rho0 - beta * z`: the parcel keeps density `rho0`,
the ambient density at `zeta` is `rho0 - beta * zeta`, so the
acceleration is `-(g * beta / rho0) * zeta`. -/
theorem boussinesq_buoyancy_accel {g beta rho0 zeta : ℝ} (hrho : rho0 ≠ 0) :
    -g * (rho0 - (rho0 - beta * zeta)) / rho0 = -(g * beta / rho0) * zeta := by
  field_simp
  ring

/-- The squared Brunt-Vaisala frequency `N^2 = g * beta / rho0` is
positive for a stable stratification (`beta > 0`) with `g, rho0 > 0`. -/
theorem brunt_vaisala_sq_pos {g beta rho0 : ℝ} (hg : 0 < g) (hbeta : 0 < beta)
    (hrho : 0 < rho0) : 0 < g * beta / rho0 := by
  exact div_pos (mul_pos hg hbeta) hrho

/-! ## B. Parcel oscillator -/

/-- Parcel oscillator: if `v` is the parcel velocity, `zeta' = v` near
`t` (`hzeta`), and the acceleration `v'` at `t` is the buoyancy
acceleration from the density contrast (`hbuoy`), then the displacement
satisfies the oscillator equation `zeta'' t = -(g * beta / rho0) * zeta t`,
where `zeta''` is the derivative of `deriv zeta`. -/
theorem boussinesq_parcel_oscillator {zeta v : ℝ → ℝ} {t : ℝ} {g beta rho0 : ℝ}
    (hrho : rho0 ≠ 0) (hzeta : ∀ᶠ s in nhds t, HasDerivAt zeta (v s) s)
    (hbuoy : HasDerivAt v (-g * (rho0 - (rho0 - beta * zeta t)) / rho0) t) :
    HasDerivAt (deriv zeta) (-(g * beta / rho0) * zeta t) t := by
  have h : -g * (rho0 - (rho0 - beta * zeta t)) / rho0
      = -(g * beta / rho0) * zeta t := boussinesq_buoyancy_accel hrho
  rw [h] at hbuoy
  exact hbuoy.congr_of_eventuallyEq (hzeta.mono fun s hs => hs.deriv)

end EarthScience
