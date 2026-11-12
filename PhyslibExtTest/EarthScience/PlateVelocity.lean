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

/-- Numeric plate: `ω = (1,2,3)`, `r = (4,5,6)`, cross `(-3,6,-3)`, dot `0`. -/
example : (2 * 6 - 3 * 5 : ℝ) * 4 + (3 * 4 - 1 * 6) * 5 + (1 * 5 - 2 * 4) * 6 = 0 :=
  EarthScience.plate_velocity_tangent (1, 2, 3) (4, 5, 6)

/-- Euler pole: `r = 2 * ω` gives velocity `(0, 0, 0)`. -/
example : (2 * (2 * 3 : ℝ) - 3 * (2 * 2), 3 * (2 * 1) - 1 * (2 * 3), 1 * (2 * 2) - 2 * (2 * 1)) =
    (0, 0, 0) := by
  norm_num [Prod.mk.injEq]

/-- General Euler-pole instance, via the theorem. -/
example (ω : ℝ × ℝ × ℝ) (c : ℝ) :
    (ω.2.1 * (c * ω.2.2) - ω.2.2 * (c * ω.2.1),
     ω.2.2 * (c * ω.1) - ω.1 * (c * ω.2.2),
     ω.1 * (c * ω.2.1) - ω.2.1 * (c * ω.1)) = (0, 0, 0) :=
  EarthScience.plate_velocity_eq_zero_at_euler_pole ω c
