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

No new definitions or results are introduced here, apart from the
private strictly-positive scale values used by the examples below.

## iii. Table of contents

- A. Conversion composition on numbers
- B. Kelvin/Celsius points and differences
- C. Degenerate cases

## iv. References

- `PhyslibExt.EarthScience.M01UnitsOrScaling`
-/

/-- Strictly positive scale `2` (no `OfNat` instance for `NNRealˣ`). -/
private noncomputable def scale2 : NNRealˣ := ⟨2, 1 / 2, by norm_num, by norm_num⟩

/-- Strictly positive scale `3` (no `OfNat` instance for `NNRealˣ`). -/
private noncomputable def scale3 : NNRealˣ := ⟨3, 1 / 3, by norm_num, by norm_num⟩

/-- Converting `5` by `2` then by `3` gives `30`. -/
example : EarthScience.unitConversion scale3 (EarthScience.unitConversion scale2 5) = 30 := by
  norm_num [EarthScience.unitConversion, scale2, scale3]

/-- The bundled inverse reverses a positive-scale conversion. -/
example (a : NNRealˣ) (x : ℝ) :
    (EarthScience.unitConversionLinearEquiv a).symm (EarthScience.unitConversion a x) = x :=
  (EarthScience.unitConversionLinearEquiv a).symm_apply_apply x

/-- The bundled affine inverse recovers the Celsius coordinate. -/
example (C : ℝ) :
    EarthScience.celsiusToKelvinAffineEquiv.symm (EarthScience.celsiusToKelvin C) = C :=
  EarthScience.celsiusToKelvinAffineEquiv.symm_apply_apply C

/-- A `5 °C` difference is a `5 K` difference, at `20 °C`. -/
example : EarthScience.celsiusToKelvin (20 + 5) - EarthScience.celsiusToKelvin 20 = 5 :=
  EarthScience.kelvin_celsius_difference

/-- The affine Kelvin map at `α = 0.3`, `C₁ = 10`, `C₂ = 20`. -/
example : EarthScience.celsiusToKelvin (0.3 * 10 + (1 - 0.3) * 20)
    = 0.3 * EarthScience.celsiusToKelvin 10 + (1 - 0.3) * EarthScience.celsiusToKelvin 20 :=
  EarthScience.kelvin_celsius_affine

/-- Zero point: `0 °C` maps to `273.15 K`. -/
example : EarthScience.celsiusToKelvin 0 = 273.15 :=
  EarthScience.kelvin_celsius_zero

/-- Degenerate conversion: converting `0` by any strictly positive scales gives `0`. -/
example : EarthScience.unitConversion scale3 (EarthScience.unitConversion scale2 0)
    = EarthScience.unitConversion (scale3 * scale2) 0 :=
  EarthScience.unitConversion_comp scale2 scale3 0

/-- Degenerate difference: a zero Celsius difference is a zero Kelvin difference. -/
example : EarthScience.celsiusToKelvin (20 + 0) - EarthScience.celsiusToKelvin 20 = 0 :=
  EarthScience.kelvin_celsius_difference
