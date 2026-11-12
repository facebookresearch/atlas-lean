/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.S03AiryIsostasy

/-!
# Airy isostasy checks

Concrete consumers of `PhyslibExt.EarthScience.S03AiryIsostasy`:
`ρc = 2700`, `ρm = 3300`, `h = 1000` (so the root is `4500`), plus the
zero-relief boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric Airy column
- B. Zero-relief boundary

## iv. References

- `PhyslibExt.EarthScience.S03AiryIsostasy`
-/

/-- Numeric Airy root: `2700 * 1000 / (3300 - 2700) = 4500`. -/
example : (2700 : ℝ) * 1000 / (3300 - 2700) = 4500 := by norm_num

/-- Numeric Airy column: the root `4500` equalizes compensation pressure
for `T = 10000`, `D = 40000`. -/
example : (2700 : ℝ) * (10000 + 1000 + 4500) + 3300 * (40000 - 10000 - 4500)
    = 2700 * 10000 + 3300 * (40000 - 10000) := by norm_num

/-- Numeric Airy column via the proved pressure theorem. -/
example : (2700 : ℝ) * (10000 + 1000 + 2700 * 1000 / (3300 - 2700))
      + 3300 * (40000 - 10000 - 2700 * 1000 / (3300 - 2700))
    = 2700 * 10000 + 3300 * (40000 - 10000) :=
  EarthScience.airy_root_pressure_eq (by norm_num) (by norm_num)

/-- Numeric converse: equal pressure at root `4500` forces the formula. -/
example : (4500 : ℝ) = 2700 * 1000 / (3300 - 2700) := by
  apply EarthScience.airy_root_of_pressure_eq (ρc := 2700) (ρm := 3300) (h := 1000)
    (T := 10000) (D := 40000) (r := 4500) (by norm_num) (by norm_num)
  norm_num

/-- Zero relief: the Airy root is `0` when `h = 0`. -/
example : (2700 : ℝ) * 0 / (3300 - 2700) = 0 := by norm_num

/-- Zero relief via the proved nonnegativity theorem. -/
example : (0 : ℝ) ≤ (2700 : ℝ) * 0 / (3300 - 2700) :=
  (EarthScience.airy_root_nonneg_pos (by norm_num) (by norm_num) (by norm_num)).1
