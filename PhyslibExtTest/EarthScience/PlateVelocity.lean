/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.PlateVelocity

/-!
# Structural geometry and plate kinematics

Concrete consumers of `PhyslibExt.EarthScience.PlateVelocity`.

## i. Overview

Numeric plate `ω = (1,2,3)`, `r = (4,5,6)` and the Euler-pole case.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.PlateVelocity`
-/

open Matrix

/-- Numeric plate: `ω = (1,2,3)`, `r = (4,5,6)` gives velocity `ω ⨯₃ r = (-3,6,-3)`. -/
example : (![1, 2, 3] : Fin 3 → ℝ) ⨯₃ ![4, 5, 6] = ![-3, 6, -3] := by
  rw [cross_apply]
  ext i
  fin_cases i <;> norm_num

/-- The numeric plate velocity is tangent to `r`, via the theorem. -/
example : ((![1, 2, 3] : Fin 3 → ℝ) ⨯₃ ![4, 5, 6]) ⬝ᵥ ![4, 5, 6] = 0 :=
  EarthScience.plate_velocity_tangent _ _

/-- Direct check of the numeric dot product: `(-3,6,-3) ⬝ᵥ (4,5,6) = 0`. -/
example : (![-3, 6, -3] : Fin 3 → ℝ) ⬝ᵥ ![4, 5, 6] = 0 := by
  norm_num [dotProduct, Fin.sum_univ_three]

/-- Euler pole: `r = 2 • ω` with `ω = (1,2,3)` gives zero velocity. -/
example : (![1, 2, 3] : Fin 3 → ℝ) ⨯₃ ((2 : ℝ) • ![1, 2, 3]) = 0 :=
  EarthScience.plate_velocity_eq_zero_at_euler_pole _ 2

/-- General Euler-pole instance, via the theorem. -/
example (ω : Fin 3 → ℝ) (c : ℝ) : ω ⨯₃ (c • ω) = 0 :=
  EarthScience.plate_velocity_eq_zero_at_euler_pole ω c
