/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.CatchmentAreaConversion

/-!
# Catchment-area-conversion checks

Concrete consumers of `PhyslibExt.EarthScience.CatchmentAreaConversion`:
with area `A = 100`, precipitation depth rate `p = 1/100`,
evaporation `e = 3/1000`, runoff `q = 2/1000` and duration `dt = 2`,
the depth storage change is `ds = 1/100`, the volume budget closes at
`2`, `50` mm of depth over area `100` is `5` cubic units, and the daily
rate over `2` days agrees with the hourly rate over `48` hours.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
boundary cases are `dt = 0` (zero duration, zero volumes) and a zero
precipitation rate, where the budget still closes with storage decreasing.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.CatchmentAreaConversion`
-/

open EarthScience

/-- Volume: area `100` times depth `1/100` is `1`. -/
example : catchmentVolume 100 (1 / 100) = 1 := by
  norm_num [catchmentVolume]

/-- Volume flux: area `100` times depth rate `1/100` is `1` per time. -/
example : catchmentVolumeFlux 100 (1 / 100) = 1 := by
  norm_num [catchmentVolumeFlux]

/-- Budget closes: with `A = 100`, `p = 1/100`, `e = 3/1000`, `q = 2/1000`,
`dt = 2`, `ds = 1/100`, the volume budget is `2 = 2`. -/
example : catchmentVolume 100 (1 / 100) + catchmentVolumeFlux 100 (3 / 1000) * 2
      + catchmentVolumeFlux 100 (2 / 1000) * 2
      = catchmentVolumeFlux 100 (1 / 100) * 2 := by
  have h := catchment_budget_closes (A := 100) (p := 1 / 100) (e := 3 / 1000)
    (q := 2 / 1000) (dt := 2) (ds := 1 / 100) (by norm_num)
  exact h

/-- Millimetres: `50` mm over area `100` is `5`. -/
example : catchmentVolume 100 (50 / 1000) = 5 := by
  norm_num [catchmentVolume]

/-- Daily/hourly: the daily rate `24` over `2` days gives the same volume
as the hourly rate over `48` hours, with area `100`. -/
example : catchmentVolumeFlux 100 (24 / 24) * (24 * 2)
    = catchmentVolumeFlux 100 24 * 2 :=
  catchment_volume_daily_hourly 100 24 2

/-- Boundary case: zero duration gives a zero storage volume. -/
example : catchmentVolume 100 ((1 / 100) * 0) = 0 := by
  norm_num [catchmentVolume]

/-- Boundary case: zero precipitation still closes the budget, with
storage decreasing by the evaporation plus runoff volumes. -/
example : catchmentVolume 100 (-(3 / 1000 + 2 / 1000) * 2)
      + catchmentVolumeFlux 100 (3 / 1000) * 2
      + catchmentVolumeFlux 100 (2 / 1000) * 2
      = catchmentVolumeFlux 100 0 * 2 := by
  have h := catchment_budget_closes (A := 100) (p := 0) (e := 3 / 1000)
    (q := 2 / 1000) (dt := 2) (ds := -(3 / 1000 + 2 / 1000) * 2) (by norm_num)
  exact h
