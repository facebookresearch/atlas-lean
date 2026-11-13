/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Global mean solar input

Earth intercepts sunlight over its cross-sectional disk of area `π R²`,
so the total intercepted power is `S₀ π R²` for solar constant `S₀`.
The sphere area is `4π R²`, four times the disk area, so the global
mean solar input is `S₀ / 4`. The factor of four is pure disk/sphere
geometry, not an atmospheric effect.

## i. Overview

The sphere area is four times the disk area by ring. Dividing the
intercepted power by the sphere area cancels `π R²` (for `R ≠ 0`) and
leaves `S₀ / 4`; multiplying the mean by the area recovers the
intercepted power.

## ii. Key results

- `EarthScience.sphere_area_eq_four_disk_area`: sphere area is four
  times disk area.
- `EarthScience.global_mean_solar_input_eq`: the global mean is `S₀ / 4`.
- `EarthScience.global_mean_solar_input_times_area`: mean times area is
  the intercepted power.

## iii. Table of contents

- A. Disk/sphere geometry and the factor of four

## iv. References

- `Real.pi_ne_zero`, `pow_ne_zero` in Mathlib.

## A. Disk/sphere geometry and the factor of four
-/

@[expose] public section

namespace EarthScience

/-- Disk/sphere geometry: the area of a sphere of radius `R` is four times
the area of its cross-sectional disk. -/
theorem sphere_area_eq_four_disk_area {R : ℝ} :
    4 * Real.pi * R ^ 2 = 4 * (Real.pi * R ^ 2) := by
  ring

/-- Global mean solar input: total intercepted power `S₀ π R²` spread over
the sphere area `4π R²` is `S₀ / 4`. -/
theorem global_mean_solar_input_eq {S₀ R : ℝ} (hR : R ≠ 0) :
    (S₀ * (Real.pi * R ^ 2)) / (4 * Real.pi * R ^ 2) = S₀ / 4 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  field_simp

/-- The global mean `S₀ / 4` times the sphere area recovers the intercepted
power `S₀ π R²`. -/
theorem global_mean_solar_input_times_area {S₀ R : ℝ} :
    (S₀ / 4) * (4 * Real.pi * R ^ 2) = S₀ * (Real.pi * R ^ 2) := by
  ring

end EarthScience
