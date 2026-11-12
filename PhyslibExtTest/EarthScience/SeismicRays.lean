/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.SeismicRays

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

/-- Symmetric refraction via stationarity: the midpoint Snell conclusion
follows from a stationarity hypothesis. -/
example (hstat : HasDerivAt
    (fun x => Real.sqrt ((3 : ℝ) ^ 2 + x ^ 2) / 2
      + Real.sqrt ((3 : ℝ) ^ 2 + (10 - x) ^ 2) / 2) 0 5) :
    5 / (2 * Real.sqrt ((3 : ℝ) ^ 2 + 5 ^ 2))
      = (10 - 5) / (2 * Real.sqrt ((3 : ℝ) ^ 2 + (10 - 5) ^ 2)) :=
  EarthScience.snell_from_stationary (a := 3) (b := 3) (D := 10) (v₁ := 2) (v₂ := 2)
    (x := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hstat

/-- Zero-length boundary: `(0 / 5) * 5 = 0`. -/
example : (0 : ℝ) / 5 * 5 = 0 :=
  (EarthScience.travel_time_segment (L := 0) (v := 5) (by norm_num) (le_refl 0)).2
