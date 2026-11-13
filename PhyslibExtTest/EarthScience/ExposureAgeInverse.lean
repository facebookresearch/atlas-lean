/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.ExposureAgeInverse

/-!
# Exposure-age-inverse checks

Concrete consumers of `PhyslibExt.EarthScience.ExposureAgeInverse`: with
`P = 10`, `lam = 1/2`, `N0 = 0`, the inventory at `t = 0` is `0`, it
increases with time, stays below the saturation value `20`, and the age
inverse recovers both the inventory and the time.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The boundary
case is `t = 0`, where the inventory is `0` and the age of `0` is `0`; a
positive-time case shows the inventory strictly increases and the
round-trip through the age inverse returns the time.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.ExposureAgeInverse`
-/

open EarthScience

/-- Boundary case: at `t = 0` the inventory with `N0 = 0` is `0`. -/
example : exposureInventory 10 (1 / 2) 0 0 = 0 := by
  simp [exposureInventory]

/-- Boundary case: the exposure age of inventory `0` is `0`. -/
example : exposureAge 10 (1 / 2) 0 = 0 := by
  simp [exposureAge]

/-- With `P = 10`, `lam = 1/2`, the inventory at `t = 1` exceeds the
inventory at `t = 0` (strict increase below saturation). -/
example : exposureInventory 10 (1 / 2) 0 0 < exposureInventory 10 (1 / 2) 0 1 :=
  exposure_inventory_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) ∈ Set.Ici 0) (by norm_num : (1 : ℝ) ∈ Set.Ici 0) (by norm_num)

/-- Saturation bound: the inventory at `t = 1` is at most `P / lam = 20`. -/
example : exposureInventory 10 (1 / 2) 0 1 ≤ 10 / (1 / 2) :=
  exposure_inventory_le_saturation (P := 10) (lam := 1 / 2) (N0 := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (by norm_num)

/-- Round-trip: the inventory at the age of an admissible inventory
`N = 5` returns `5`. -/
example : exposureInventory 10 (1 / 2) 0 (exposureAge 10 (1 / 2) 5) = 5 :=
  exposure_age_inventory (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Round-trip: the age of the inventory at `t = 1` returns `1`. -/
example : exposureAge 10 (1 / 2) (exposureInventory 10 (1 / 2) 0 1) = 1 :=
  exposure_inventory_age (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuous: the inventory at `t = 1` is not already at saturation,
so the strict-monotonicity and inverse statements have content. -/
example : exposureInventory 10 (1 / 2) 0 1 < 20 := by
  have h := exposure_inventory_le_saturation (P := 10) (lam := 1 / 2) (N0 := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (by norm_num)
  have hstrict : exposureInventory 10 (1 / 2) 0 1 <
      exposureInventory 10 (1 / 2) 0 2 :=
    exposure_inventory_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
      (by norm_num : (1 : ℝ) ∈ Set.Ici 0) (by norm_num : (2 : ℝ) ∈ Set.Ici 0) (by norm_num)
  have h2 := exposure_inventory_le_saturation (P := 10) (lam := 1 / 2) (N0 := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2 (by norm_num)
  linarith
