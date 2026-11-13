/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.SedimentAges

/-!
# Sediment-age checks

Concrete consumers of `PhyslibExt.EarthScience.SedimentAges`: a numeric age, a
monotonicity instance, the depth-age inverse in both directions, the surface boundary
`d = 0`, and the age difference between two horizons.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With `v = 2`, depth `6` has
age `3`, deeper is older, and horizons at depths `4` and `10` differ in age by `3`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.SedimentAges`
-/

open EarthScience

/-- Numeric age: with `v = 2`, depth `6` has age `3`. -/
example : sedimentAge 2 6 = 3 := by norm_num [sedimentAge]

/-- Monotonicity: with `v = 2`, a deeper depth has a larger age. -/
example (a b : ℝ) (ha : a ∈ Set.Ici (0 : ℝ)) (hb : b ∈ Set.Ici (0 : ℝ))
    (hab : a < b) : sedimentAge 2 a < sedimentAge 2 b :=
  sediment_age_strictMonoOn 2 (by norm_num) ha hb hab

/-- The depth-age inverse at `v = 2`, `t = 3`: the sediment of age `3` lies at depth `6`,
which has age `3`. -/
example : sedimentDepth 2 3 = 6 ∧ sedimentAge 2 (sedimentDepth 2 3) = 3 :=
  ⟨by norm_num [sedimentDepth], sediment_depth_age_inverse 2 3 (by norm_num)⟩

/-- The converse inverse at `v = 2`, `d = 5`. -/
example : sedimentDepth 2 (sedimentAge 2 5) = 5 :=
  sedimentDepth_sedimentAge 2 5 (by norm_num)

/-- Boundary case: the surface, depth `0`, has age `0`; buried sediment has nonnegative age. -/
example : sedimentAge 2 0 = 0 ∧ 0 ≤ sedimentAge 2 7 :=
  ⟨sedimentAge_zero 2, sedimentAge_nonneg (by norm_num) (by norm_num)⟩

/-- Horizons at depths `4` and `10`, with `v = 2`, differ in age by `(10 - 4) / 2 = 3`. -/
example : sedimentAge 2 10 - sedimentAge 2 4 = 3 := by
  rw [sedimentAge_sub]
  norm_num
