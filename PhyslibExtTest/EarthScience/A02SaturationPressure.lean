/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.A02SaturationPressure

/-!
# Saturation-pressure checks

Concrete consumers of `PhyslibExt.EarthScience.A02SaturationPressure`:
the public shape of the derivative theorem, positivity at unit
parameters, and strict monotonicity at standard values
(`es0 = 6.11`, `L / Rv = 5423`, `T0 = 273.15`).

## i. Overview

These are elaboration and non-vacuity checks, not new results. At
`T = 300` the standard values give `es ≈ 36.1` with a positive derivative.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Derivative and positivity
- B. Strict monotonicity

## iv. References

- `PhyslibExt.EarthScience.A02SaturationPressure`
-/

/-- Public shape of the saturation-pressure derivative theorem. -/
example {es0 L Rv T0 : ℝ} {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun T => es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T)))
      ((es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T))) * L / (Rv * T ^ 2)) T :=
  EarthScience.hasDerivAt_saturation_pressure hT

/-- Positivity at unit parameters and `T = 1`. -/
example : 0 < (1 * Real.exp ((1 / 1) * (1 / 1 - 1 / 1))) * 1 / (1 * (1 : ℝ) ^ 2) :=
  EarthScience.saturation_pressure_deriv_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Strict monotonicity at standard values. -/
example : StrictMonoOn
    (fun T => (6.11 : ℝ) * Real.exp (((5423 : ℝ) / 1) * (1 / 273.15 - 1 / T)))
    (Set.Ioi 0) :=
  EarthScience.saturation_pressure_strictMono (es0 := 6.11) (L := 5423) (Rv := 1)
    (T0 := 273.15) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Saturation pressure at the reference temperature equals `es0`. -/
example : (6.11 : ℝ) * Real.exp ((5423 : ℝ) * (1 / 273.15 - 1 / 273.15)) = 6.11 := by
  norm_num
