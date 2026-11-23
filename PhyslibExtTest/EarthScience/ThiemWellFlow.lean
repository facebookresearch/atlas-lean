/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import PhyslibExt.EarthScience.ThiemWellFlow

/-!
# Thiem well-flow checks

Concrete consumers of `PhyslibExt.EarthScience.ThiemWellFlow`: pumping
`Q = 100`, transmissivity `T = 10`, radii `r1 = 1` and `r2 = exp 1` (so
`log (r2 / r1) = 1` and the head rise is `5 / π`), plus the zero-pumping,
equal-radii and outward-increase boundaries.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric Thiem flow
- B. Boundary cases

## iv. References

- `PhyslibExt.EarthScience.ThiemWellFlow`
-/

/-- Numeric Thiem flow: `Q = 100`, `T = 10`, `r1 = 1`, `r2 = exp 1`
gives head rise `5 / π`. -/
example : ((0 : ℝ) + 100 * Real.log (Real.exp 1) / (2 * Real.pi * 10)) -
    ((0 : ℝ) + 100 * Real.log 1 / (2 * Real.pi * 10)) = 5 / Real.pi := by
  have h := EarthScience.thiem_head_difference (Q := 100) (T := 10) (C := 0)
    (r1 := 1) (r2 := Real.exp 1) (by norm_num) (by norm_num) (Real.exp_pos 1)
  rw [h]
  have hlog : Real.log (Real.exp 1 / 1) = 1 := by
    rw [div_one]
    exact Real.log_exp 1
  rw [hlog]
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- Thiem flow: head increases outward for pumping `Q = 100`, `T = 10`,
`r1 = 1`, `r2 = 2`. -/
example : 0 ≤ ((0 : ℝ) + 100 * Real.log 2 / (2 * Real.pi * 10)) -
    ((0 : ℝ) + 100 * Real.log 1 / (2 * Real.pi * 10)) :=
  EarthScience.thiem_head_difference_nonneg (Q := 100) (T := 10) (C := 0)
    (r1 := 1) (r2 := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Zero-pumping boundary: `Q = 0` gives zero head difference. -/
example : ((0 : ℝ) + 0 * Real.log 2 / (2 * Real.pi * 10)) -
    ((0 : ℝ) + 0 * Real.log 1 / (2 * Real.pi * 10)) = 0 :=
  EarthScience.thiem_head_difference_zero_pumping (T := 10) (C := 0)
    (r1 := 1) (r2 := 2) (by norm_num) (by norm_num) (by norm_num)

/-- Equal-radii boundary: `r1 = r2 = 1` gives zero head difference. -/
example : ((0 : ℝ) + 100 * Real.log 1 / (2 * Real.pi * 10)) -
    ((0 : ℝ) + 100 * Real.log 1 / (2 * Real.pi * 10)) = 0 :=
  EarthScience.thiem_head_difference_equal_radii (Q := 100) (T := 10) (C := 0)
    (r := 1) (by norm_num) (by norm_num)
