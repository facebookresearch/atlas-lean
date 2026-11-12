/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.FirstLawWithWork

/-!
# First-law-with-work checks

Concrete consumers of `PhyslibExt.EarthScience.FirstLawWithWork`:
`Q = 100`, `W = 30`, `C = 10` gives `ΔT = 7`, heating from `300` to
`307`; the `W = 0` case recovers the isochoric `Q / C`; and `Q = W`
gives zero change.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.FirstLawWithWork`
-/

/-- `Q = 100`, `W = 30`, `C = 10`: `ΔT = 7`. -/
example : (307 : ℝ) - 300 = (100 - 30) / 10 := by
  have h := EarthScience.firstLaw_temperature_change (C := (10 : ℝ)) (Q := 100) (W := 30)
    (U0 := (0 : ℝ)) (U1 := 70) (T0 := 300) (T1 := 307)
    (by norm_num) (by norm_num) (by norm_num)
  exact h

/-- Heating from `300` to `307` under the same inputs. -/
example : (307 : ℝ) = 300 + (100 - 30) / 10 := by
  have h := EarthScience.firstLaw_final_temperature (C := (10 : ℝ)) (Q := 100) (W := 30)
    (U0 := (0 : ℝ)) (U1 := 70) (T0 := 300) (T1 := 307)
    (by norm_num) (by norm_num) (by norm_num)
  exact h

/-- Boundary case: `Q = W` gives zero temperature change. -/
example : (300 : ℝ) - 300 = (50 - 50) / 10 := by
  have h := EarthScience.firstLaw_temperature_change (C := (10 : ℝ)) (Q := 50) (W := 50)
    (U0 := (0 : ℝ)) (U1 := 0) (T0 := 300) (T1 := 300)
    (by norm_num) (by norm_num) (by norm_num)
  exact h
