/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Dipole inclination: `tan I = 2 * tan λ`

For dipole components `B_r = 2 * C * cos θ / r ^ 3` and
`B_θ = C * sin θ / r ^ 3`, the signed ratio `B_r / B_θ` is `2 * tan λ`;
for the Earth-like orientation `C < 0`, the geomagnetic inclination
satisfies `tan I = 2 * tan λ`.

## i. Overview

`θ` is the magnetic colatitude (angle from the `θ = 0` end of the dipole
axis), `λ = π / 2 - θ` the magnetic latitude, `r > 0` the distance, and
`C ≠ 0` the dipole moment factor (units chosen so `B` is a magnetic flux
density). `B_r` is positive outward and `B_θ` positive toward increasing
colatitude. The signed identity `B_r / B_θ = 2 * cot θ = 2 * tan λ`
(`tan (π / 2 - θ) = cos θ / sin θ`) holds for either sign of `C`.

Geomagnetic inclination uses the downward vertical component `Z = -B_r`
and the horizontal intensity `H = |B_θ|`, with `tan I = Z / H`. On the
physical colatitude domain `0 < θ < π`, `B_θ < 0` exactly when `C < 0`
(moment pointing toward `θ = π`), and then `tan I = B_r / B_θ = 2 * tan λ`.
With `θ` measured from the geomagnetic north pole this is the orientation
of Earth's present field, which dips downward in the north; for `C > 0`
the sign flips, `tan I = -2 * tan λ`.

Model field, not proof Earth is dipolar. The singular source `r = 0` is
excluded from every theorem. The signed ratio excludes only the axis
`sin θ = 0`, where `B_θ` vanishes; it covers the magnetic equator
`θ = π / 2`, where both sides are `0`. The equator and pole component
values are also stated separately.

## ii. Key results

- `EarthScience.dipole_component_ratio`: signed `B_r / B_θ = 2 * tan λ`.
- `EarthScience.dipole_tan_inclination`: `tan I = Z / H = 2 * tan λ` for
  `C < 0` and `0 < θ < π`.
- `EarthScience.dipole_equator`: at `θ = π / 2`, `B_r = 0`, `B_θ = C / r ^ 3`.
- `EarthScience.dipole_pole`: at `θ = 0`, `B_θ = 0`, `B_r = 2 * C / r ^ 3`.

## iii. Table of contents

- A. Dipole inclination

## iv. References

- W. Lowrie, *Fundamentals of Geophysics*, 2nd ed., Cambridge University
  Press (2007), chapter "Geomagnetism and paleomagnetism": the
  geomagnetic elements (`Z` positive downward, horizontal intensity `H`,
  `tan I = Z / H`) and the dipole relation `tan I = 2 * tan λ`.
- `Real.tan_eq_sin_div_cos`, `Real.sin_pi_div_two_sub`,
  `Real.cos_pi_div_two_sub` in Mathlib.

## A. Dipole inclination
-/

@[expose] public section

namespace EarthScience

/-- Signed dipole component ratio: `B_r / B_θ = 2 * tan λ` where
`λ = π / 2 - θ` is the magnetic latitude, `B_r = 2 * C * cos θ / r ^ 3`,
`B_θ = C * sin θ / r ^ 3`, for either sign of `C`. Only the axis
`sin θ = 0` is excluded; at the equator both sides are `0`. This is
`tan I` only when `B_θ < 0`; see `dipole_tan_inclination`. -/
theorem dipole_component_ratio {C r θ : ℝ} (hr : 0 < r) (hC : C ≠ 0)
    (hsin : Real.sin θ ≠ 0) :
    (2 * C * Real.cos θ / r ^ 3) / (C * Real.sin θ / r ^ 3)
      = 2 * Real.tan (Real.pi / 2 - θ) := by
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr.ne'
  have hden : C * Real.sin θ / r ^ 3 ≠ 0 :=
    div_ne_zero (mul_ne_zero hC hsin) hr3
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  field_simp

/-- Dipole inclination: with downward vertical component `Z = -B_r` and
horizontal intensity `H = |B_θ|`, `tan I = Z / H = 2 * tan λ`. The moment
factor is `C < 0` (moment toward `θ = π`; Earth's present orientation when
`θ` is the colatitude from the geomagnetic north pole), and `0 < θ < π`. -/
theorem dipole_tan_inclination {C r θ : ℝ} (hr : 0 < r) (hC : C < 0)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    -(2 * C * Real.cos θ / r ^ 3) / |C * Real.sin θ / r ^ 3|
      = 2 * Real.tan (Real.pi / 2 - θ) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hBθ : C * Real.sin θ / r ^ 3 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hC hsin) (pow_pos hr 3)
  rw [abs_of_neg hBθ, neg_div_neg_eq]
  exact dipole_component_ratio hr hC.ne hsin.ne'

set_option linter.unusedVariables false in
/-- Dipole at the magnetic equator (`θ = π / 2`), away from the source
(`r > 0`): `B_r = 0`, `B_θ = C / r ^ 3`. -/
theorem dipole_equator {C r : ℝ} (hr : 0 < r) :
    2 * C * Real.cos (Real.pi / 2) / r ^ 3 = 0 ∧
      C * Real.sin (Real.pi / 2) / r ^ 3 = C / r ^ 3 := by
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

set_option linter.unusedVariables false in
/-- Dipole at the magnetic pole (`θ = 0`), away from the source (`r > 0`):
`B_θ = 0`, `B_r = 2 * C / r ^ 3`. -/
theorem dipole_pole {C r : ℝ} (hr : 0 < r) :
    C * Real.sin 0 / r ^ 3 = 0 ∧ 2 * C * Real.cos 0 / r ^ 3 = 2 * C / r ^ 3 := by
  simp

end EarthScience
