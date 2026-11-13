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

Earth intercepts sunlight over its cross-sectional disk, so with the
standard disk-area formula `π R²` the total intercepted power is
`S₀ π R²` for solar constant `S₀`. Spreading that power over the
standard sphere-area formula `4π R²` gives the global mean solar input
`S₀ / 4`. Physically the factor of four comes from disk/sphere geometry
rather than from the atmosphere; this file takes both area formulas as
given and proves only algebraic identities between them. It does not
derive either area from a measure.

## i. Overview

The expression `4π R²` is `4 · (π R²)` by reassociation. Dividing the
intercepted power by `4π R²` cancels `π R²` (for `R ≠ 0`) and leaves
`S₀ / 4`; multiplying the mean by `4π R²` recovers the intercepted
power.

## ii. Key results

- `EarthScience.four_mul_pi_mul_sq_assoc`: the algebraic identity
  `4 * π * R ^ 2 = 4 * (π * R ^ 2)` (no area is derived).
- `EarthScience.global_mean_solar_input_eq`: the global mean is `S₀ / 4`.
- `EarthScience.global_mean_solar_input_times_area`: mean times `4π R²`
  is the intercepted power.

## iii. Table of contents

- A. The area formulas and the factor of four

## iv. References

- `Real.pi_ne_zero`, `pow_ne_zero` in Mathlib.

## A. The area formulas and the factor of four
-/

@[expose] public section

namespace EarthScience

/-- Algebraic identity (reassociation): `4 * π * R ^ 2 = 4 * (π * R ^ 2)`.
Read with the standard formulas `4π R²` for the area of a sphere and `π R²`
for the area of its cross-sectional disk, it restates the first formula as
four times the second; the formulas themselves are assumed, not derived. -/
lemma four_mul_pi_mul_sq_assoc {R : ℝ} :
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
