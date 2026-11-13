/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.DipoleInclination

/-!
# Dipole inclination checks

Concrete consumers of `PhyslibExt.EarthScience.DipoleInclination`:
`θ = π / 6` (latitude `π / 3`, `tan I = 2√3`), `C = 1`, `r = 1`, the
ratio at the equator (both sides `0`), plus the equator and pole branches.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric inclination
- B. Equator and pole

## iv. References

- `PhyslibExt.EarthScience.DipoleInclination`
-/

/-- Numeric inclination: `θ = π / 6`, `C = 1`, `r = 1` gives
`B_r / B_θ = 2 * tan (π / 3)`. -/
example : (2 * (1 : ℝ) * Real.cos (Real.pi / 6) / 1 ^ 3)
    / (1 * Real.sin (Real.pi / 6) / 1 ^ 3)
    = 2 * Real.tan (Real.pi / 2 - Real.pi / 6) :=
  EarthScience.dipole_inclination_ratio (by norm_num) (by norm_num)
    (by rw [Real.sin_pi_div_six]; norm_num)

/-- Numeric inclination value: `2 * tan (π / 3) = 2√3`. -/
example : 2 * Real.tan (Real.pi / 3) = 2 * Real.sqrt 3 := by
  rw [Real.tan_pi_div_three]

/-- Equator ratio: `θ = π / 2`, `C = 1`, `r = 1` is covered by the ratio
theorem. -/
example : (2 * (1 : ℝ) * Real.cos (Real.pi / 2) / 1 ^ 3)
    / (1 * Real.sin (Real.pi / 2) / 1 ^ 3)
    = 2 * Real.tan (Real.pi / 2 - Real.pi / 2) :=
  EarthScience.dipole_inclination_ratio (by norm_num) (by norm_num)
    (by rw [Real.sin_pi_div_two]; norm_num)

/-- Equator ratio value: both sides are `0`. -/
example : (2 * (1 : ℝ) * Real.cos (Real.pi / 2) / 1 ^ 3)
      / (1 * Real.sin (Real.pi / 2) / 1 ^ 3) = 0 ∧
    2 * Real.tan (Real.pi / 2 - Real.pi / 2) = 0 := by
  simp

/-- Equator: `B_r = 0`, `B_θ = C / r ^ 3`. -/
example : 2 * (1 : ℝ) * Real.cos (Real.pi / 2) / 1 ^ 3 = 0 ∧
    1 * Real.sin (Real.pi / 2) / 1 ^ 3 = 1 / 1 ^ 3 :=
  EarthScience.dipole_equator (by norm_num)

/-- Pole: `B_θ = 0`, `B_r = 2 * C / r ^ 3`. -/
example : (1 : ℝ) * Real.sin 0 / 1 ^ 3 = 0 ∧
    2 * 1 * Real.cos 0 / 1 ^ 3 = 2 * 1 / 1 ^ 3 :=
  EarthScience.dipole_pole (by norm_num)
