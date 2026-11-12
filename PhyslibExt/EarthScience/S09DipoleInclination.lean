/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Dipole inclination: `tan I = 2 * tan λ`

For aligned dipole components `B_r = 2 * C * cos θ / r ^ 3` and
`B_θ = C * sin θ / r ^ 3`, `tan inclination = 2 * tan latitude` on a
nonsingular branch.

## i. Overview

`θ` is the magnetic colatitude (angle from the dipole axis), `λ = π / 2 - θ`
the magnetic latitude, `r > 0` the distance, `C ≠ 0` the dipole moment
factor (units chosen so `B` is a magnetic flux density). The inclination
satisfies `tan I = B_r / B_θ = 2 * cot θ = 2 * tan λ`, since
`tan (π / 2 - θ) = cos θ / sin θ`. Signs are tied to the magnetic axis.
Model field, not proof Earth is dipolar. The singular source `r = 0` and
the axis/equator branches where a component vanishes are excluded from
the ratio theorem and treated separately.

## ii. Key results

- `EarthScience.dipole_inclination_ratio`: `B_r / B_θ = 2 * tan λ`.
- `EarthScience.dipole_equator`: at `θ = π / 2`, `B_r = 0`, `B_θ = C / r ^ 3`.
- `EarthScience.dipole_pole`: at `θ = 0`, `B_θ = 0`, `B_r = 2 * C / r ^ 3`.

## iii. Table of contents

- A. Dipole inclination

## iv. References

- `Real.tan_eq_sin_div_cos`, `Real.sin_pi_div_two_sub`,
  `Real.cos_pi_div_two_sub` in Mathlib.

## A. Dipole inclination
-/

@[expose] public section

namespace EarthScience

/-- Dipole inclination: `B_r / B_θ = 2 * tan λ` where `λ = π / 2 - θ` is the
magnetic latitude, `B_r = 2 * C * cos θ / r ^ 3`, `B_θ = C * sin θ / r ^ 3`. -/
theorem dipole_inclination_ratio {C r θ : ℝ} (hr : 0 < r) (hC : C ≠ 0)
    (hsin : Real.sin θ ≠ 0) (hcos : Real.cos θ ≠ 0) :
    (2 * C * Real.cos θ / r ^ 3) / (C * Real.sin θ / r ^ 3)
      = 2 * Real.tan (Real.pi / 2 - θ) := by
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr.ne'
  have hden : C * Real.sin θ / r ^ 3 ≠ 0 :=
    div_ne_zero (mul_ne_zero hC hsin) hr3
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  field_simp

/-- Dipole at the magnetic equator (`θ = π / 2`): `B_r = 0`, `B_θ = C / r ^ 3`. -/
theorem dipole_equator {C r : ℝ} :
    2 * C * Real.cos (Real.pi / 2) / r ^ 3 = 0 ∧
      C * Real.sin (Real.pi / 2) / r ^ 3 = C / r ^ 3 := by
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Dipole at the magnetic pole (`θ = 0`): `B_θ = 0`, `B_r = 2 * C / r ^ 3`. -/
theorem dipole_pole {C r : ℝ} :
    C * Real.sin 0 / r ^ 3 = 0 ∧ 2 * C * Real.cos 0 / r ^ 3 = 2 * C / r ^ 3 := by
  simp

end EarthScience
