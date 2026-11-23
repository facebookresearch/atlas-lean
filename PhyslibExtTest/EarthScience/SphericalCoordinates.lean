/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.SphericalCoordinates

/-!
# Earth coordinates, distance, and map geometry

Concrete consumers of `PhyslibExt.EarthScience.SphericalCoordinates`.

## i. Overview

Equator, pole, and a generic numeric point.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.SphericalCoordinates`
-/

/-- Equator at `φ = 0`, `λ = 0`: point `(R, 0, 0)`, squared norm `R²`. -/
example : ((6371 : ℝ) * Real.cos 0 * Real.cos 0) ^ 2 +
    ((6371 : ℝ) * Real.cos 0 * Real.sin 0) ^ 2 + ((6371 : ℝ) * Real.sin 0) ^ 2 = (6371 : ℝ) ^ 2 :=
  EarthScience.spherical_point_norm_sq

/-- North pole `φ = π / 2`: point `(0, 0, R)`, squared norm `R²`. -/
example : ((1 : ℝ) * Real.cos (Real.pi / 2) * Real.cos 0) ^ 2 +
    ((1 : ℝ) * Real.cos (Real.pi / 2) * Real.sin 0) ^ 2 + ((1 : ℝ) * Real.sin (Real.pi / 2)) ^ 2 =
      (1 : ℝ) ^ 2 :=
  EarthScience.spherical_point_norm_sq

/-- Generic numeric point `R = 6371`, `φ = 0.5`, `λ = 1.0`. -/
example : ((6371 : ℝ) * Real.cos 0.5 * Real.cos 1.0) ^ 2 +
    ((6371 : ℝ) * Real.cos 0.5 * Real.sin 1.0) ^ 2 + ((6371 : ℝ) * Real.sin 0.5) ^ 2 = (6371 : ℝ) ^
      2 :=
  EarthScience.spherical_point_norm_sq
