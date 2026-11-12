/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.P16BoussinesqParcel

/-!
# Boussinesq parcel checks

Concrete consumers of `PhyslibExt.EarthScience.P16BoussinesqParcel`:
the buoyancy formula at `g = 9.81, beta = 0.02, rho0 = 1025, zeta = 10`,
the stable/unstable sign boundary, and the oscillator form for a
linear-displacement parcel.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At the
concrete parameters the buoyancy acceleration is
`-(9.81 * 0.02 / 1025) * 10`, and `N^2 = 9.81 * 0.02 / 1025 > 0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete buoyancy and stability
- B. Oscillator and boundary cases

## iv. References

- `PhyslibExt.EarthScience.P16BoussinesqParcel`
-/

/-- Public shape of the buoyancy-acceleration theorem. -/
example {g beta rho0 zeta : ℝ} (hrho : rho0 ≠ 0) :
    -g * (rho0 - (rho0 - beta * zeta)) / rho0 = -(g * beta / rho0) * zeta :=
  EarthScience.boussinesq_buoyancy_accel hrho

/-- Concrete buoyancy: admissible nonzero parameters. -/
example : -(9.81 : ℝ) * (1025 - (1025 - 0.02 * 10)) / 1025
    = -(9.81 * 0.02 / 1025) * 10 :=
  EarthScience.boussinesq_buoyancy_accel (show (1025 : ℝ) ≠ 0 by norm_num)

/-- Stable stratification gives positive `N^2`. -/
example : 0 < (9.81 : ℝ) * 0.02 / 1025 :=
  EarthScience.brunt_vaisala_sq_pos (by norm_num) (by norm_num) (by norm_num)

/-- Uniform density (`beta = 0`) gives zero buoyancy acceleration. -/
example {g rho0 zeta : ℝ} (hrho : rho0 ≠ 0) :
    -g * (rho0 - (rho0 - (0 : ℝ) * zeta)) / rho0 = 0 := by
  rw [EarthScience.boussinesq_buoyancy_accel hrho]
  simp

/-- Oscillator form for a parcel whose velocity obeys the buoyancy law. -/
example {zeta v : ℝ → ℝ} {t : ℝ} {g beta rho0 : ℝ} (hrho : rho0 ≠ 0)
    (hbuoy : HasDerivAt v (-g * (rho0 - (rho0 - beta * zeta t)) / rho0) t) :
    HasDerivAt v (-(g * beta / rho0) * zeta t) t :=
  EarthScience.boussinesq_parcel_oscillator hrho hbuoy
