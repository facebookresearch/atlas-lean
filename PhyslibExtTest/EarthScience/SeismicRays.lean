/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.SeismicRays
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Seismic ray checks

Concrete consumers of `PhyslibExt.EarthScience.SeismicRays`:
a straight segment `L = 100`, `v = 5` (travel time `20`), the symmetric
two-layer case `a = b = 3`, `D = 10`, `x = 5`, `v = 2`, and the
zero-length boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Straight segment
- B. Symmetric refraction
- C. Zero-length boundary

## iv. References

- `PhyslibExt.EarthScience.SeismicRays`
-/

/-- Straight segment: `100 / 5 = 20`, and `20 * 5 = 100`. -/
example : (0 : ℝ) ≤ (100 : ℝ) / 5 ∧ (100 : ℝ) / 5 * 5 = 100 :=
  EarthScience.travel_time_segment (L := 100) (v := 5) (by norm_num) (by norm_num)

/-- Symmetric refraction: at the midpoint, Snell's law gives equal
ray parameters `5 / √34 = 5 / √34`. -/
example : (5 : ℝ) / Real.sqrt (3 ^ 2 + 5 ^ 2)
    = (10 - 5) / Real.sqrt (3 ^ 2 + (10 - 5) ^ 2) := by
  apply EarthScience.snell_equal_speed (a := 3) (b := 3) (D := 10) (v := 2) (x := 5)
    (by norm_num)
  norm_num

/-- Symmetric refraction via stationarity: the travel time
`√(3² + x²) / 2 + √(3² + (10 - x)²) / 2` has derivative `0` at the midpoint `x = 5`
(constructed here, not assumed), so `snell_from_stationary` gives the midpoint
Snell conclusion. -/
example : 5 / (2 * Real.sqrt ((3 : ℝ) ^ 2 + 5 ^ 2))
      = (10 - 5) / (2 * Real.sqrt ((3 : ℝ) ^ 2 + (10 - 5) ^ 2)) := by
  have h1 : (3 : ℝ) ^ 2 + 5 ^ 2 ≠ 0 := by norm_num
  have h2 : (3 : ℝ) ^ 2 + (10 - 5) ^ 2 ≠ 0 := by norm_num
  have hd1 := (((hasDerivAt_pow 2 (5 : ℝ)).const_add ((3 : ℝ) ^ 2)).sqrt h1).div_const 2
  have hDx : HasDerivAt (fun x : ℝ => 10 - x) (-1) 5 := (hasDerivAt_id' 5).const_sub 10
  have hd2 := (((hDx.fun_pow 2).const_add ((3 : ℝ) ^ 2)).sqrt h2).div_const 2
  have hstat : HasDerivAt
      (fun x => Real.sqrt ((3 : ℝ) ^ 2 + x ^ 2) / 2
        + Real.sqrt ((3 : ℝ) ^ 2 + (10 - x) ^ 2) / 2) 0 5 := by
    convert hd1.fun_add hd2 using 1
    norm_num
    ring
  exact EarthScience.snell_from_stationary (a := 3) (b := 3) (D := 10) (v₁ := 2) (v₂ := 2)
    (x := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hstat

/-- Zero-length boundary: `(0 / 5) * 5 = 0`. -/
example : (0 : ℝ) / 5 * 5 = 0 :=
  (EarthScience.travel_time_segment (L := 0) (v := 5) (by norm_num) (le_refl 0)).2
