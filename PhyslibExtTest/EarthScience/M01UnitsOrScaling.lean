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

/-- Converting `5` by `2` then by `3` is converting by `6`. -/
example : EarthScience.unitConversion 3 (EarthScience.unitConversion 2 5)
    = EarthScience.unitConversion (3 * 2) 5 :=
  EarthScience.unitConversion_comp 2 3 5

/-- A `5 °C` difference is a `5 K` difference, at `20 °C`. -/
example : EarthScience.celsiusToKelvin (20 + 5) - EarthScience.celsiusToKelvin 20 = 5 :=
  EarthScience.kelvin_celsius_difference

/-- The affine Kelvin map at `α = 0.3`, `C₁ = 10`, `C₂ = 20`. -/
example : EarthScience.celsiusToKelvin (0.3 * 10 + (1 - 0.3) * 20)
    = 0.3 * EarthScience.celsiusToKelvin 10 + (1 - 0.3) * EarthScience.celsiusToKelvin 20 :=
  EarthScience.kelvin_celsius_affine

/-- Freezing point: `0 °C` maps to `273.15 K`. -/
example : EarthScience.celsiusToKelvin 0 = 273.15 :=
  EarthScience.kelvin_celsius_zero

/-- Degenerate conversion: converting `0` by any nonnegative scales gives `0`. -/
example : EarthScience.unitConversion 3 (EarthScience.unitConversion 2 0)
    = EarthScience.unitConversion (3 * 2) 0 :=
  EarthScience.unitConversion_comp 2 3 0

/-- Degenerate difference: a zero Celsius difference is a zero Kelvin difference. -/
example : EarthScience.celsiusToKelvin (20 + 0) - EarthScience.celsiusToKelvin 20 = 0 :=
  EarthScience.kelvin_celsius_difference
