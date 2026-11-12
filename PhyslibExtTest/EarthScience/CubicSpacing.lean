/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.CubicSpacing

/-!
# Cubic spacing checks

Concrete consumers of `PhyslibExt.EarthScience.CubicSpacing`:
`a = 0.4`, planes `(100)`, `(110)`, `(111)`, plus the `(200)` plane.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric spacing
- B. Higher-order plane

## iv. References

- `PhyslibExt.EarthScience.CubicSpacing`
-/

/-- Numeric spacing: `(100)` gives `d = a`. -/
example : (0.4 : ℝ) / Real.sqrt ((1 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2) = 0.4 :=
  EarthScience.cubic_spacing_100 (by norm_num)

/-- Numeric spacing: `(110)` gives `d = a / √2`. -/
example : (0.4 : ℝ) / Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2 + 0 ^ 2)
    = 0.4 / Real.sqrt 2 :=
  EarthScience.cubic_spacing_110 (by norm_num)

/-- Numeric spacing: `(111)` gives `d = a / √3`. -/
example : (0.4 : ℝ) / Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2 + 1 ^ 2)
    = 0.4 / Real.sqrt 3 :=
  EarthScience.cubic_spacing_111 (by norm_num)

/-- Numeric spacing: `(200)` gives `d = a / 2`, via the squared formula. -/
example : ((0.4 : ℝ) / Real.sqrt (((2 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2)) ^ 2
    = 0.4 ^ 2 / (((2 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2) :=
  EarthScience.cubic_spacing_sq (a := 0.4) (h := 2) (k := 0) (l := 0)
    (by norm_num) (by norm_num)

/-- Spacing positivity for `(111)`. -/
example : 0 < (0.4 : ℝ) / Real.sqrt (((1 : ℤ) : ℝ) ^ 2 + ((1 : ℤ) : ℝ) ^ 2 + ((1 : ℤ) : ℝ) ^ 2) :=
  EarthScience.cubic_spacing_pos (a := 0.4) (h := 1) (k := 1) (l := 1)
    (by norm_num) (by norm_num)
