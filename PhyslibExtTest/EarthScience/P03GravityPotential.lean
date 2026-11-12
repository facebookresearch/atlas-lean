/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.P03GravityPotential

/-!
# Point-mass potential checks

Concrete consumers of `PhyslibExt.EarthScience.P03GravityPotential`:
`G = 2`, `M = 3`, `r = 2` (so `Φ = -3`, `dΦ/dr = 3 / 2`), and the
zero-mass boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric point mass
- B. Zero-mass boundary

## iv. References

- `PhyslibExt.EarthScience.P03GravityPotential`
-/

/-- Numeric point mass: `dΦ/dr = 3 / 2` at `r = 2`. -/
example : HasDerivAt (fun r => -(2 : ℝ) * 3 / r) ((2 : ℝ) * 3 / 2 ^ 2) 2 :=
  EarthScience.hasDerivAt_pointMass_potential (by norm_num)

/-- Numeric point mass: potential value and radial acceleration. -/
example : -(2 : ℝ) * 3 / 2 = -3 ∧ -(2 * 3 / (2 : ℝ) ^ 2) = -(3 / 2) := by
  norm_num

/-- Radial acceleration for the numeric point mass. -/
example : HasDerivAt (fun r => -(2 : ℝ) * 3 / r) ((2 : ℝ) * 3 / 2 ^ 2) 2 ∧
    -(deriv (fun s => -(2 : ℝ) * 3 / s) 2) = -(2 : ℝ) * 3 / 2 ^ 2 ∧
    -(2 : ℝ) * 3 / 2 ^ 2 < 0 :=
  EarthScience.pointMass_radial_acceleration (by norm_num) (by norm_num) (by norm_num)

/-- Zero-mass boundary: the potential is identically zero, derivative zero. -/
example (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r => -(2 : ℝ) * 0 / r) 0 r := by
  have h := EarthScience.hasDerivAt_pointMass_potential (G := 2) (M := 0) (r := r) hr
  simpa using h
