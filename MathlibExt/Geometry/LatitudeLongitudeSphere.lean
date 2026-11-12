/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Latitude/longitude coordinates lie on the sphere

The Cartesian point with latitude `φ`, longitude `lon`, and radius `R`,
`(R cos φ cos lon, R cos φ sin lon, R sin φ)`, has squared radius `R ^ 2`.

## i. Overview

Expand the `Fin 3` sum and factor: the first two terms give
`R ^ 2 * cos ^ 2 φ * (cos ^ 2 lon + sin ^ 2 lon) = R ^ 2 * cos ^ 2 φ`,
and adding `R ^ 2 * sin ^ 2 φ` gives `R ^ 2` by `cos ^ 2 φ + sin ^ 2 φ = 1`.

## ii. Key results

- `EarthScience.lat_lon_on_sphere`: latitude/longitude coordinates lie on
  the sphere of radius `R`.

## iii. References

- `Real.cos_sq_add_sin_sq`, `Fin.sum_univ_three` (Mathlib).
-/

@[expose] public section

open scoped BigOperators

namespace EarthScience

/-- Cartesian latitude/longitude coordinates lie on the sphere: the point
`(R cos φ cos lon, R cos φ sin lon, R sin φ)` has squared radius `R ^ 2`. -/
theorem lat_lon_on_sphere (R φ lon : ℝ) :
    ∑ i, (![R * Real.cos φ * Real.cos lon, R * Real.cos φ * Real.sin lon,
      R * Real.sin φ] i) ^ 2 = R ^ 2 := by
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hlon : Real.cos lon ^ 2 + Real.sin lon ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq lon
  have hphi : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq φ
  calc (R * Real.cos φ * Real.cos lon) ^ 2 +
        (R * Real.cos φ * Real.sin lon) ^ 2 + (R * Real.sin φ) ^ 2
      = R ^ 2 * (Real.cos φ ^ 2 * (Real.cos lon ^ 2 + Real.sin lon ^ 2) +
          Real.sin φ ^ 2) := by ring
    _ = R ^ 2 * (Real.cos φ ^ 2 * 1 + Real.sin φ ^ 2) := by rw [hlon]
    _ = R ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by ring
    _ = R ^ 2 := by rw [hphi, mul_one]

end EarthScience
