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
`M = 1000`, `k = 10`, `c = 0` (magnitude difference `2 / 3`),
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

/-- Numeric magnitude shift: `M = 1000`, `k = 10`, `c = 0` gives `2 / 3`. -/
example :
    EarthScience.momentMagnitude 0 (10 * 1000) - EarthScience.momentMagnitude 0 1000 = 2 / 3 := by
  rw [EarthScience.momentMagnitude_difference (M := 1000) (k := 10) (c := 0)
    (by norm_num) (by norm_num), Real.logb_self_eq_one (by norm_num), mul_one]

/-- Unit-scale boundary: `k = 1` gives difference `0`. -/
example : EarthScience.momentMagnitude 2 (1 * 5) - EarthScience.momentMagnitude 2 5 = 0 := by
  rw [EarthScience.momentMagnitude_difference (M := 5) (k := 1) (c := 2)
    (by norm_num) (by norm_num), Real.logb_one, mul_zero]

/-- Unit moment with `c = 9`: `Mw(1) = -6`. -/
example : EarthScience.momentMagnitude 9 1 = -6 := by
  rw [EarthScience.momentMagnitude_one]
  norm_num

/-- Hanks-Kanamori zero-point for `M₀` in dyne·cm, `c = 16.05`: one dyne·cm
has `Mw = -10.7`, the additive constant of `Mw = (2 / 3) * log₁₀ M₀ - 10.7`. -/
example : EarthScience.momentMagnitude 16.05 1 = -10.7 := by
  rw [EarthScience.momentMagnitude_one]
  norm_num
