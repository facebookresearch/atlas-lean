/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.MomentMagnitude
import Mathlib.Tactic.NormNum

/-!
# Moment-magnitude checks

Concrete consumers of `PhyslibExt.EarthScience.MomentMagnitude`:
`M = 1000`, `k = 10`, `c = 0` (magnitude difference `(2 / 3) * log₁₀ 10`),
the `k = 1` boundary (difference `0`), unit moment with `c = 9`
(`Mw(1) = -6`), and the Hanks-Kanamori dyne·cm zero-point `c = 16.05`
(`Mw(1) = -10.7`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric magnitude shift
- B. Unit-moment and unit-scale boundaries

## iv. References

- `PhyslibExt.EarthScience.MomentMagnitude`
-/

/-- Numeric magnitude shift: `M = 1000`, `k = 10`, `c = 0`. -/
example : (2 / 3 : ℝ) * (Real.log (10 * 1000) / Real.log 10 - 0)
      - (2 / 3 : ℝ) * (Real.log 1000 / Real.log 10 - 0)
      = (2 / 3 : ℝ) * (Real.log 10 / Real.log 10) :=
  EarthScience.momentMagnitude_difference (M := 1000) (k := 10) (c := 0)
    (by norm_num) (by norm_num)

/-- Unit-scale boundary: `k = 1` gives difference `0`. -/
example : (2 / 3 : ℝ) * (Real.log (1 * 5) / Real.log 10 - 2)
      - (2 / 3 : ℝ) * (Real.log 5 / Real.log 10 - 2) = 0 := by
  have h := EarthScience.momentMagnitude_difference (M := 5) (k := 1) (c := 2)
    (by norm_num) (by norm_num)
  rw [one_mul, Real.log_one, zero_div, mul_zero] at h
  rw [one_mul]
  exact h

/-- Unit moment with `c = 9`: `Mw(1) = -6`. -/
example : (2 / 3 : ℝ) * (Real.log 1 / Real.log 10 - 9) = -6 := by
  rw [show ((2 / 3 : ℝ) * (Real.log 1 / Real.log 10 - 9))
      = -(2 / 3 : ℝ) * 9 from EarthScience.momentMagnitude_one]
  norm_num

/-- Hanks-Kanamori zero-point for `M₀` in dyne·cm, `c = 16.05`: one dyne·cm
has `Mw = -10.7`, the additive constant of `Mw = (2 / 3) * log₁₀ M₀ - 10.7`. -/
example : (2 / 3 : ℝ) * (Real.log 1 / Real.log 10 - 16.05) = -10.7 := by
  rw [show ((2 / 3 : ℝ) * (Real.log 1 / Real.log 10 - 16.05))
      = -(2 / 3 : ℝ) * 16.05 from EarthScience.momentMagnitude_one]
  norm_num
