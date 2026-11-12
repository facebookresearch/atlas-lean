/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Structural geometry and plate kinematics

## i. Overview

Given angular velocity `ω`, the rigid plate velocity `v = ω ⨯ r` (triples, cross product written
  out componentwise) is tangent to the sphere: `v ⬝ r = 0`. At the Euler pole, where `r` is
  parallel to `ω`, the velocity vanishes. No subtraction or composition of finite rotations is
  involved.

## ii. Key results

- `EarthScience.plate_velocity_tangent`: `v ⬝ r = 0`.
- `EarthScience.plate_velocity_eq_zero_at_euler_pole`: velocity vanishes at the Euler pole.

## iii. Table of contents

- A. Plate velocity tangency

## iv. References

- `ring` in Mathlib (tactic).
-/

@[expose] public section

namespace EarthScience

/-- Rigid plate velocity is tangent: for angular velocity `ω` and position
`r` (as triples), `v = ω ⨯ r` satisfies `v ⬝ r = 0`. -/
theorem plate_velocity_tangent (ω r : ℝ × ℝ × ℝ) :
    (ω.2.1 * r.2.2 - ω.2.2 * r.2.1) * r.1 +
      (ω.2.2 * r.1 - ω.1 * r.2.2) * r.2.1 +
      (ω.1 * r.2.1 - ω.2.1 * r.1) * r.2.2 = 0 := by
  ring

/-- At the Euler pole, `r` parallel to `ω`, the plate velocity vanishes. -/
theorem plate_velocity_eq_zero_at_euler_pole (ω : ℝ × ℝ × ℝ) (c : ℝ) :
    (ω.2.1 * (c * ω.2.2) - ω.2.2 * (c * ω.2.1),
     ω.2.2 * (c * ω.1) - ω.1 * (c * ω.2.2),
     ω.1 * (c * ω.2.1) - ω.2.1 * (c * ω.1)) = (0, 0, 0) := by
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

end EarthScience
