/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.C06Isochrons

/-!
# Isochron checks

Concrete consumers of `PhyslibExt.EarthScience.C06Isochrons`: a numeric
isochron slope and age, and the `t = 0` boundary where the slope is `0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`λ = 1/10`, `t = 10`, `b = 7/10`, parent ratios `1` and `3`, the slope is
`exp(1) - 1` and the recovered age is `10`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.C06Isochrons`
-/

/-- Numeric isochron slope with `λ = 1/10`, `t = 10`. -/
example : (((7/10 : ℝ) + 3 * (Real.exp ((1/10) * 10) - 1)) -
    ((7/10 : ℝ) + 1 * (Real.exp ((1/10) * 10) - 1))) / (3 - 1) =
    Real.exp ((1/10) * 10) - 1 :=
  EarthScience.isochron_slope_eq (1/10) 10 (7/10) 1 3
    ((7/10) + 1 * (Real.exp ((1/10) * 10) - 1))
    ((7/10) + 3 * (Real.exp ((1/10) * 10) - 1))
    (by norm_num) rfl rfl

/-- Numeric isochron age recovery: the slope identifies `t = 10`. -/
example : Real.log (1 + ((((7/10 : ℝ) + 3 * (Real.exp ((1/10) * 10) - 1)) -
    ((7/10 : ℝ) + 1 * (Real.exp ((1/10) * 10) - 1))) / (3 - 1))) / (1/10) = 10 :=
  EarthScience.isochron_age_eq (1/10) 10 (7/10) 1 3
    ((7/10) + 1 * (Real.exp ((1/10) * 10) - 1))
    ((7/10) + 3 * (Real.exp ((1/10) * 10) - 1))
    (by norm_num) (by norm_num) rfl rfl

/-- Boundary case `t = 0`: the slope is `0`, since `exp(0) - 1 = 0`. -/
example : (((7/10 : ℝ) + 3 * (Real.exp ((1/10) * 0) - 1)) -
    ((7/10 : ℝ) + 1 * (Real.exp ((1/10) * 0) - 1))) / (3 - 1) =
    Real.exp ((1/10) * 0) - 1 :=
  EarthScience.isochron_slope_eq (1/10) 0 (7/10) 1 3
    ((7/10) + 1 * (Real.exp ((1/10) * 0) - 1))
    ((7/10) + 3 * (Real.exp ((1/10) * 0) - 1))
    (by norm_num) rfl rfl
