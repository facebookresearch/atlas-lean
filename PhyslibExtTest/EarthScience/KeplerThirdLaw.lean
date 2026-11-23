/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.KeplerThirdLaw

/-!
# Orbital forcing groundwork and elementary planetary mechanics

Concrete consumers of `PhyslibExt.EarthScience.KeplerThirdLaw`.

## i. Overview

Unit-parameter Kepler case (`G = M = r = v = 1`, `T = 2π`) and the circular speed, plus
non-degenerate cases with distinct, non-unit parameters that exercise the `G * M` denominator and
the cubic radius dependence.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.KeplerThirdLaw`
-/

/-- Unit case: `G = M = r = v = 1`, `T = 2π` gives `T² = 4π²`. -/
example : (2 * Real.pi : ℝ) ^ 2 = 4 * Real.pi ^ 2 * 1 ^ 3 / (1 * 1) :=
  EarthScience.kepler_third_law (G := 1) (M := 1) (r := 1) (v := 1) (T := 2 * Real.pi)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Unit circular speed: `v = √(1) = 1`. -/
example : (1 : ℝ) = Real.sqrt (1 * 1 / 1) :=
  EarthScience.kepler_circular_speed (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    norm_num)

/-- Non-degenerate case: `G = 2`, `M = 3`, `r = 6`, `v = 1` satisfy `v² = GM / r`, and
`T = 2πr / v = 12π` gives `T² = 4π² · 6³ / (2 · 3) = 144π²`. -/
example : (12 * Real.pi : ℝ) ^ 2 = 144 * Real.pi ^ 2 :=
  (EarthScience.kepler_third_law (G := 2) (M := 3) (r := 6) (v := 1) (T := 12 * Real.pi)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring)).trans
    (by ring)

/-- Non-degenerate circular speed: `G = 2`, `M = 8`, `r = 4`, `v = 2` satisfy `v² = GM / r`, so
`√(GM / r) = √4 = 2`. -/
example : Real.sqrt (2 * 8 / 4) = (2 : ℝ) :=
  (EarthScience.kepler_circular_speed (G := 2) (M := 8) (r := 4) (v := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
