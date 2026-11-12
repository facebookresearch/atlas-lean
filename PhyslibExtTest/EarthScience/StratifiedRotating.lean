/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.StratifiedRotating

/-!
# Stratified-rotating-column capstone checks

Concrete consumers of `PhyslibExt.EarthScience.StratifiedRotating`:
atmospheric `N² > 0` at `g = 10, θ = 300, dθ = 1`, oceanic `N² > 0`
at `g = 10, ρ₀ = 1025, dρ = -1`, the geostrophic value `-4 / 41`,
the equator rejection, and the north/south sign cases.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Stratification and geostrophy

## iv. References

- `PhyslibExt.EarthScience.StratifiedRotating`
-/

/-- Atmospheric `N² > 0` at `g = 10, θ = 300, dθ = 1`. -/
example : 0 < (10 / 300 : ℝ) * 1 :=
  EarthScience.bruntVaisala_atmosphere_pos (by norm_num) (by norm_num) (by norm_num)

/-- Oceanic `N² > 0` at `g = 10, ρ₀ = 1025, dρ = -1`. -/
example : 0 < -(10 / 1025 : ℝ) * (-1) :=
  EarthScience.bruntVaisala_ocean_pos (by norm_num) (by norm_num) (by norm_num)

/-- Geostrophic value `-4 / 41`. -/
example : -(1 / (1025 * (1 / 10000 : ℝ))) * (1 / 100) = -4 / 41 :=
  EarthScience.geostrophic_wind_value

/-- Equator rejection: `ρ * 0 = 0`. -/
example : (1025 : ℝ) * 0 = 0 :=
  EarthScience.geostrophic_rejects_equator (ρ := 1025)

/-- North: `f = 10⁻⁴, dp / dx = 0.01` gives `v < 0`. -/
example : -(1 / (1025 * (1 / 10000 : ℝ))) * (1 / 100) < 0 :=
  (EarthScience.geostrophic_sign_cases (ρ := 1025) (f := 1 / 10000)
    (dpdx := 1 / 100) (by norm_num) (by norm_num)).1 (by norm_num)

/-- South: `f = -10⁻⁴, dp / dx = 0.01` gives `v > 0`. -/
example : 0 < -(1 / (1025 * (-(1 / 10000 : ℝ)))) * (1 / 100) :=
  (EarthScience.geostrophic_sign_cases (ρ := 1025) (f := -(1 / 10000))
    (dpdx := 1 / 100) (by norm_num) (by norm_num)).2 (by norm_num)
