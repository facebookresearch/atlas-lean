/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.P18KeplerThirdLaw

/-!
# Orbital forcing groundwork and elementary planetary mechanics

Concrete consumers of `PhyslibExt.EarthScience.P18KeplerThirdLaw`.

## i. Overview

Unit-parameter Kepler case (`G = M = r = v = 1`, `T = 2π`) and the circular speed.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.P18KeplerThirdLaw`
-/

/-- Unit case: `G = M = r = v = 1`, `T = 2π` gives `T² = 4π²`. -/
example : (2 * Real.pi : ℝ) ^ 2 = 4 * Real.pi ^ 2 * 1 ^ 3 / (1 * 1) :=
  EarthScience.kepler_third_law (G := 1) (M := 1) (r := 1) (v := 1) (T := 2 * Real.pi)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Unit circular speed: `v = √(1) = 1`. -/
example : (1 : ℝ) = Real.sqrt (1 * 1 / 1) :=
  EarthScience.kepler_circular_speed (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    norm_num)
