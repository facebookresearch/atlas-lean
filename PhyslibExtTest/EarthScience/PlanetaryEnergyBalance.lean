/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.PlanetaryEnergyBalance

/-!
# Planetary energy balance checks

Concrete consumers of `PhyslibExt.EarthScience.PlanetaryEnergyBalance`:
`sigma = 1, S = 64, alpha = 0` (equilibrium `T = 2`), full albedo,
and uniqueness: any `T >= 0` with `T^4 = 16` is `2`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.PlanetaryEnergyBalance`
-/

/-- Existence: `sigma = 1, S = 16, alpha = 0` has a nonnegative equilibrium. -/
example : ∃ T : ℝ, 0 ≤ T ∧ (1:ℝ) * T ^ 4 = (1 - (0:ℝ)) * 16 / 4 :=
  EarthScience.planetaryEnergyBalance_equilibrium_exists
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Uniqueness pins an arbitrary equilibrium: for `sigma = 1, S = 64, alpha = 0`,
any `T >= 0` with `T^4 = 16` equals the concrete equilibrium `2`. -/
example {T : ℝ} (hT : 0 ≤ T) (h : T ^ 4 = 16) : T = 2 :=
  EarthScience.planetaryEnergyBalance_equilibrium_unique (σ := 1) (S := 64) (α := 0)
    (by norm_num) hT (by norm_num) (by rw [h]; norm_num) (by norm_num)

/-- Full albedo: any nonnegative equilibrium is `0`. -/
example {T : ℝ} (hT : 0 ≤ T) (h : (1:ℝ) * T ^ 4 = (1 - (1:ℝ)) * 16 / 4) : T = 0 :=
  EarthScience.planetaryEnergyBalance_full_albedo (by norm_num) (by norm_num) hT h

/-- Witness: `sigma = 1, S = 4, alpha = 0` gives `T = 1`. -/
example : ∃ T : ℝ, 0 ≤ T ∧ (1:ℝ) * T ^ 4 = (1 - (0:ℝ)) * 4 / 4 ∧ T = 1 :=
  EarthScience.planetaryEnergyBalance_witness
