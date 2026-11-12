/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Earth coordinates, distance, and map geometry

## i. Overview

On a sphere of radius `R`, the Cartesian point `R * (cos φ cos λ, cos φ sin λ, sin φ)` for
  geocentric latitude `φ` (radians) and longitude `λ` has squared norm `R²`. The geodetic ellipsoid
  is a separate bridge; pole longitude non-uniqueness is not an issue for the squared norm.

## ii. Key results

- `EarthScience.spherical_point_norm_sq`: the squared norm is `R²`.

## iii. Table of contents

- A. Spherical point norm

## iv. References

- `Real.cos_sq_add_sin_sq` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Spherical coordinates lie on the sphere: for radius `R`, geocentric
latitude `φ` and longitude `lam`, the squared norm of
`R * (cos φ cos lam, cos φ sin lam, sin φ)` is `R ^ 2`. -/
theorem spherical_point_norm_sq {R φ lam : ℝ} :
    (R * Real.cos φ * Real.cos lam) ^ 2 +
      (R * Real.cos φ * Real.sin lam) ^ 2 + (R * Real.sin φ) ^ 2 = R ^ 2 := by
  have hlam := Real.cos_sq_add_sin_sq lam
  have hphi := Real.cos_sq_add_sin_sq φ
  linear_combination R ^ 2 * Real.cos φ ^ 2 * hlam + R ^ 2 * hphi

end EarthScience
