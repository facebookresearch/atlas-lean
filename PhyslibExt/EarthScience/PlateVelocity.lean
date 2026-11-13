/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Structural geometry and plate kinematics

## i. Overview

Vectors in `ℝ³` are `Fin 3 → ℝ`, with Mathlib's cross product `⨯₃` and dot product `⬝ᵥ`.
Given angular velocity `ω`, the rigid plate velocity `v = ω ⨯₃ r` is tangent to the sphere:
`v ⬝ᵥ r = 0`. At the Euler pole, where `r = c • ω` is parallel to `ω`, the velocity vanishes.
No subtraction or composition of finite rotations is involved.

## ii. Key results

- `EarthScience.plate_velocity_tangent`: `(ω ⨯₃ r) ⬝ᵥ r = 0`.
- `EarthScience.plate_velocity_eq_zero_at_euler_pole`: `ω ⨯₃ (c • ω) = 0`.

## iii. Table of contents

- A. Plate velocity tangency

## iv. References

- `Mathlib.LinearAlgebra.CrossProduct`: `dot_cross_self` and `cross_self`.
-/

@[expose] public section

namespace EarthScience

open Matrix

/-- Rigid plate velocity is tangent to the sphere: for angular velocity `ω` and position `r`,
the velocity `v = ω ⨯₃ r` satisfies `v ⬝ᵥ r = 0`. -/
theorem plate_velocity_tangent (ω r : Fin 3 → ℝ) : (ω ⨯₃ r) ⬝ᵥ r = 0 := by
  rw [dotProduct_comm]
  exact dot_cross_self ω r

/-- At the Euler pole, where the position `r = c • ω` is parallel to the angular velocity `ω`,
the plate velocity `ω ⨯₃ r` vanishes. -/
theorem plate_velocity_eq_zero_at_euler_pole (ω : Fin 3 → ℝ) (c : ℝ) :
    ω ⨯₃ (c • ω) = 0 := by
  rw [map_smul, cross_self, smul_zero]

end EarthScience
