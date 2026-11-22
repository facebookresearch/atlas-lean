/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.UniformSpherePotential

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform-sphere potential checks

Concrete consumers of `PhyslibExt.EarthScience.UniformSpherePotential`:
`G = 3`, `M = 5`, `R = 2`. The interior value at the surface is
`-15 / 4 * (3 - 1) = -15 / 2`, the exterior value is `-15 / 2`, and
both derivatives are `15 / 4`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. A second
case `G = M = R = 1` checks value `-1` and derivative `1`. A last check
confirms the normalization: with `M = 4 * π * ρ * R ^ 3 / 3`, the interior
formula is the homogeneous-sphere potential `-2 * π * G * ρ * (R ^ 2 - r ^ 2 / 3)`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete surface matching

## iv. References

- `PhyslibExt.EarthScience.UniformSpherePotential`
-/

/-- Public shape of the surface-matching theorem. -/
example {G M R : ℝ} (hR : 0 < R) :
    (fun r => -G * M / (2 * R) * (3 - (r / R) ^ 2)) R = -G * M / R ∧
    HasDerivAt (fun r => -G * M / (2 * R) * (3 - (r / R) ^ 2)) (G * M / R ^ 2) R ∧
    HasDerivAt (fun r => -G * M / r) (G * M / R ^ 2) R :=
  EarthScience.uniform_sphere_potential_matches_at_surface hR

/-- Concrete case `G = 3`, `M = 5`, `R = 2`: value `-15 / 2`,
derivative `15 / 4` for both formulas. -/
example :
    (fun r => -(3 : ℝ) * 5 / (2 * 2) * (3 - (r / 2) ^ 2)) 2 = -3 * 5 / 2 ∧
    HasDerivAt (fun r => -(3 : ℝ) * 5 / (2 * 2) * (3 - (r / 2) ^ 2)) (3 * 5 / 2 ^ 2) 2 ∧
    HasDerivAt (fun r => -(3 : ℝ) * 5 / r) (3 * 5 / 2 ^ 2) 2 := by
  exact EarthScience.uniform_sphere_potential_matches_at_surface
    (G := (3 : ℝ)) (M := (5 : ℝ)) (R := (2 : ℝ)) (by norm_num)

/-- Unit case `G = M = R = 1`: value `-1`, derivative `1`. -/
example :
    (fun r => -(1 : ℝ) * 1 / (2 * 1) * (3 - (r / 1) ^ 2)) 1 = -1 * 1 / 1 ∧
    HasDerivAt (fun r => -(1 : ℝ) * 1 / (2 * 1) * (3 - (r / 1) ^ 2)) (1 * 1 / 1 ^ 2) 1 ∧
    HasDerivAt (fun r => -(1 : ℝ) * 1 / r) (1 * 1 / 1 ^ 2) 1 := by
  exact EarthScience.uniform_sphere_potential_matches_at_surface
    (G := (1 : ℝ)) (M := (1 : ℝ)) (R := (1 : ℝ)) (by norm_num)

/-- The concrete numbers: `-3 * 5 / 2 = -(15 / 2)` and `3 * 5 / 2 ^ 2 = 15 / 4`. -/
example : -3 * 5 / (2 : ℝ) = -(15 / 2 : ℝ) ∧ 3 * 5 / (2 : ℝ) ^ 2 = (15 / 4 : ℝ) := by
  constructor <;> norm_num

/-- Normalization: with `M = 4 * π * ρ * R ^ 3 / 3`, the interior formula is the
homogeneous-sphere potential `-2 * π * G * ρ * (R ^ 2 - r ^ 2 / 3)`. -/
example {G ρ R r : ℝ} (hR : R ≠ 0) :
    -G * (4 * Real.pi * ρ * R ^ 3 / 3) / (2 * R) * (3 - (r / R) ^ 2) =
      -2 * Real.pi * G * ρ * (R ^ 2 - r ^ 2 / 3) := by
  field_simp
  ring
