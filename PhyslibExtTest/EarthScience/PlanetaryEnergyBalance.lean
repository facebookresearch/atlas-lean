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
and uniqueness.

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
  EarthScience.equilibrium_exists (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The equilibrium for `sigma = 1, S = 64, alpha = 0` is `T = 2`: uniqueness pins it. -/
example : (2:ℝ) = 2 :=
  EarthScience.equilibrium_unique (σ := 1) (S := 64) (α := 0) (T₁ := 2) (T₂ := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Full albedo: any nonnegative equilibrium is `0`. -/
example {T : ℝ} (hT : 0 ≤ T) (h : (1:ℝ) * T ^ 4 = (1 - (1:ℝ)) * 16 / 4) : T = 0 :=
  EarthScience.full_albedo (by norm_num) (by norm_num) hT h

/-- Witness: `sigma = 1, S = 4, alpha = 0` gives `T = 1`. -/
example : ∃ T : ℝ, 0 ≤ T ∧ (1:ℝ) * T ^ 4 = (1 - (0:ℝ)) * 4 / 4 ∧ T = 1 :=
  EarthScience.witness

