/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.BlackbodyFlux

open MeasureTheory intervalIntegral

/-!
# Integrated blackbody flux checks

Concrete consumers of `PhyslibExt.EarthScience.BlackbodyFlux`.

## i. Overview

Concrete case `σ = 1`, `T = 2`: the integrated flux is `16`.
Boundary cases: `σ = 0` gives flux `0`, and `σ = 3`, `T = -2` gives
`48` (the `T⁴` makes the flux independent of the sign of `T`).

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete and boundary checks

## iv. References

- `PhyslibExt.EarthScience.BlackbodyFlux`
-/

/-- Concrete case: `σ = 1`, `T = 2`, integrated flux `16`. -/
example : ∫ θ in (0 : ℝ)..(Real.pi / 2),
    ((1 : ℝ) * (2 : ℝ) ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ) = 16 := by
  rw [EarthScience.integrated_blackbody_flux_eq]
  norm_num

/-- Boundary case: `σ = 0` gives flux `0`. -/
example : ∫ θ in (0 : ℝ)..(Real.pi / 2),
    ((0 : ℝ) * (300 : ℝ) ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ) = 0 := by
  rw [EarthScience.integrated_blackbody_flux_eq]
  simp

/-- Sign of `T` does not matter: `σ = 3`, `T = -2` gives flux `48`. -/
example : ∫ θ in (0 : ℝ)..(Real.pi / 2),
    ((3 : ℝ) * (-2 : ℝ) ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ) = 48 := by
  rw [EarthScience.integrated_blackbody_flux_eq]
  norm_num

/-- Nonnegativity at a negative temperature: `σ = 3`, `T = -2`. -/
example : 0 ≤ (3 : ℝ) * (-2 : ℝ) ^ 4 :=
  EarthScience.integrated_blackbody_flux_nonneg (by norm_num)
