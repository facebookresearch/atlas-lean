/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.M01UnitsOrScaling

/-!
# Unit-scale conversion and temperature-scale checks

Concrete consumers of `PhyslibExt.EarthScience.M01UnitsOrScaling`:
a numeric conversion composition, Kelvin/Celsius zero points and
temperature differences, and degenerate cases (`x = 0`, `Δ = 0`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Conversion composition on numbers
- B. Kelvin/Celsius points and differences
- C. Degenerate cases

## iv. References

- `PhyslibExt.EarthScience.M01UnitsOrScaling`
-/

/-- Converting `5` by `2` then by `3` is converting by `6`, and `6 > 0`. -/
example : (3 : ℝ) * (2 * 5) = (3 * 2) * 5 ∧ (0 : ℝ) < 3 * 2 :=
  EarthScience.unit_conversion_comp (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)

/-- A `5 °C` difference is a `5 K` difference, at `20 °C`. -/
example : (20 + 5 + 273.15 : ℝ) - (20 + 273.15) = 5 :=
  EarthScience.kelvin_celsius_difference

/-- The affine Kelvin map at `α = 0.3`, `C₁ = 10`, `C₂ = 20`. -/
example : (0.3 * 10 + (1 - 0.3) * 20 + 273.15 : ℝ)
    = 0.3 * (10 + 273.15) + (1 - 0.3) * (20 + 273.15) :=
  (EarthScience.kelvin_celsius_affine).1

/-- Freezing point: `0 °C` maps to `273.15 K`. -/
example : (0 + 273.15 : ℝ) = 273.15 :=
  (EarthScience.kelvin_celsius_affine (C₁ := 0) (C₂ := 0) (α := 0)).2

/-- Degenerate conversion: converting `0` by any positive scales gives `0`. -/
example : (3 : ℝ) * (2 * 0) = (3 * 2) * 0 :=
  (EarthScience.unit_conversion_comp (a := 2) (b := 3) (x := 0) (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)).1

/-- Degenerate difference: a zero Celsius difference is a zero Kelvin difference. -/
example : (20 + 0 + 273.15 : ℝ) - (20 + 273.15) = 0 :=
  EarthScience.kelvin_celsius_difference
