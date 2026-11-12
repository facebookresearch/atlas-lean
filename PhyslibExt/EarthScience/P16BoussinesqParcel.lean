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
reference density, times `-g`. The oscillator theorem converts a
buoyancy-law derivative hypothesis for the parcel velocity into the
form `zeta'' = -(g * beta / rho0) * zeta`.

## ii. Key results

- `EarthScience.boussinesq_buoyancy_accel`: buoyancy acceleration formula.
- `EarthScience.brunt_vaisala_sq_pos`: `N^2 > 0` for stable stratification.
- `EarthScience.boussinesq_parcel_oscillator`: velocity derivative in
  oscillator form.

## iii. Table of contents

- A. Buoyancy acceleration and Brunt-Vaisala frequency
- B. Parcel oscillator

## iv. References

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

/-- If the parcel velocity `v` (derivative of displacement `zeta`) has
derivative equal to the buoyancy acceleration from the density contrast,
then it satisfies the oscillator form `zeta'' = -(g * beta / rho0) * zeta`. -/
theorem boussinesq_parcel_oscillator {zeta v : ℝ → ℝ} {t : ℝ} {g beta rho0 : ℝ}
    (hrho : rho0 ≠ 0)
    (hbuoy : HasDerivAt v (-g * (rho0 - (rho0 - beta * zeta t)) / rho0) t) :
    HasDerivAt v (-(g * beta / rho0) * zeta t) t := by
  have h : -g * (rho0 - (rho0 - beta * zeta t)) / rho0
      = -(g * beta / rho0) * zeta t := boussinesq_buoyancy_accel hrho
  rw [h] at hbuoy
  exact hbuoy

end EarthScience
