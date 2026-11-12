/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.C08SedimentAges

/-!
# Sediment-age checks

Concrete consumers of `PhyslibExt.EarthScience.C08SedimentAges`: a
numeric monotonicity instance, the depth-age inverse, and the surface
boundary `d = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`v = 2`, depth `6` has age `3`, and deeper is older.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.C08SedimentAges`
-/

/-- Monotonicity: with `v = 2`, a deeper depth has a larger age. -/
example (a b : ℝ) (ha : a ∈ Set.Ici (0 : ℝ)) (hb : b ∈ Set.Ici (0 : ℝ))
    (hab : a < b) : a / 2 < b / 2 :=
  EarthScience.sediment_age_strictMonoOn 2 (by norm_num) ha hb hab

/-- The depth-age inverse is used at `v = 2`, `t = 3`: `(2*3)/2 = 3`. -/
example : (2 : ℝ) * 3 / 2 = 3 :=
  EarthScience.sediment_depth_age_inverse 2 3 (by norm_num)

/-- Boundary case: surface depth `0` has age `0/2 = 0`. -/
example : (0 : ℝ) / 2 = 0 := by norm_num
