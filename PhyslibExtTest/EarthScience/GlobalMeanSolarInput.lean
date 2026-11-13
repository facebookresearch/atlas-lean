/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GlobalMeanSolarInput

/-!
# Global mean solar input checks

Concrete consumers of `PhyslibExt.EarthScience.GlobalMeanSolarInput`.

## i. Overview

Concrete case `S₀ = 1361`, `R = 6371000`: the global mean is `340.25`.
Boundary cases: `R = 0` is excluded from the division theorem, so the
area identity (which holds at `R = 0`) and the mean-times-area identity
(which holds at `R = 0`) are checked there instead; `S₀ = 0` gives mean
`0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete and boundary checks

## iv. References

- `PhyslibExt.EarthScience.GlobalMeanSolarInput`
-/

/-- Concrete case: `S₀ = 1361`, `R = 6371000`, global mean `340.25`. -/
example : ((1361 : ℝ) * (Real.pi * (6371000 : ℝ) ^ 2)) /
    (4 * Real.pi * (6371000 : ℝ) ^ 2) = 1361 / 4 :=
  EarthScience.global_mean_solar_input_eq (by norm_num)

/-- Boundary case `R = 0`: sphere area is four times disk area (both `0`). -/
example : 4 * Real.pi * (0 : ℝ) ^ 2 = 4 * (Real.pi * (0 : ℝ) ^ 2) :=
  EarthScience.sphere_area_eq_four_disk_area

/-- Boundary case `R = 0`: mean times area recovers intercepted power
(both `0`). -/
example : ((1361 : ℝ) / 4) * (4 * Real.pi * (0 : ℝ) ^ 2) =
    1361 * (Real.pi * (0 : ℝ) ^ 2) :=
  EarthScience.global_mean_solar_input_times_area

/-- Boundary case `S₀ = 0`: global mean `0`. -/
example : ((0 : ℝ) * (Real.pi * (6371000 : ℝ) ^ 2)) /
    (4 * Real.pi * (6371000 : ℝ) ^ 2) = 0 / 4 :=
  EarthScience.global_mean_solar_input_eq (by norm_num)
