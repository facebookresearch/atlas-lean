/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Tactic.Ring

/-!
# Unit-scale conversions and affine temperature scales

Unit conversions for magnitudes of one dimension are multiplications
by nonnegative scales, and temperature differences transform linearly
while absolute Celsius-to-Kelvin conversion is affine.

## i. Overview

A conversion is indexed by a strictly positive scale `a : NNRealˣ`
(units of `NNReal`): `unitConversion a x = (a : ℝ) * x`, so strict
positivity is carried by the type and the scale `0` is excluded.
Converting by `a` and then by `b` is converting by the composite
scale `b * a` in `NNRealˣ`, which stays strictly positive. Kelvin and Celsius are related
by the named map `celsiusToKelvin C = C + 273.15`: a temperature
difference `Δ` in Celsius is the same difference in kelvin, while an
absolute temperature shifts by the `273.15` offset. The zero point
`celsiusToKelvin 0 = 273.15` is its own theorem, so consumers never
supply dummy arguments for it. No new dimensions type is introduced;
the statements are real algebra on the existing carriers.

## ii. Key results

- `EarthScience.unitConversion`: the conversion map for a
  strictly positive scale.
- `EarthScience.unitConversion_comp`: conversions compose, with the
  composite scale in `NNRealˣ`.
- `EarthScience.celsiusToKelvin`: the Celsius-to-Kelvin map.
- `EarthScience.kelvin_celsius_difference`: Kelvin differences equal
  Celsius differences.
- `EarthScience.kelvin_celsius_affine`: the Celsius-to-Kelvin map
  preserves affine combinations.
- `EarthScience.kelvin_celsius_zero`: `0 °C` (the freezing point of
  water) maps to `273.15 K`.

## iii. Table of contents

- A. Unit-scale conversions
- B. Temperature differences, affine map, and zero point

## iv. References

- `NNReal.coe_mul`, `ring` (Mathlib), which close all four proofs.
  No Physlib dimension API is used: the milestone is the real
  algebra of scales and offsets, not a new quantity base.

## A. Unit-scale conversions
-/

@[expose] public section

namespace EarthScience

/-- Unit-scale conversion by a strictly positive scale `a`: `C_a(x) = a * x`.
Scales are units of `NNReal`, so strict positivity is carried by the
type and the scale `0` is excluded. -/
def unitConversion (a : NNRealˣ) (x : ℝ) : ℝ := (a : ℝ) * x

/-- Unit-scale conversions compose: converting by `a` then by `b` is
converting by the composite scale `b * a` in `NNRealˣ`. Strictly
positive scales stay strictly positive under multiplication. -/
theorem unitConversion_comp (a b : NNRealˣ) (x : ℝ) :
    unitConversion b (unitConversion a x) = unitConversion (b * a) x := by
  simp only [unitConversion, Units.val_mul, NNReal.coe_mul]
  ring

/-! ## B. Temperature differences, affine map, and zero point -/

/-- Celsius-to-Kelvin conversion: `T_K = T_C + 273.15`. -/
def celsiusToKelvin (C : ℝ) : ℝ := C + 273.15

/-- Temperature differences transform linearly: the Kelvin value of
`C + Δ` minus the Kelvin value of `C` is exactly `Δ`. -/
theorem kelvin_celsius_difference {C Δ : ℝ} :
    celsiusToKelvin (C + Δ) - celsiusToKelvin C = Δ := by
  simp only [celsiusToKelvin]
  ring

/-- The Celsius-to-Kelvin map preserves affine combinations. -/
theorem kelvin_celsius_affine {C₁ C₂ α : ℝ} :
    celsiusToKelvin (α * C₁ + (1 - α) * C₂)
      = α * celsiusToKelvin C₁ + (1 - α) * celsiusToKelvin C₂ := by
  simp only [celsiusToKelvin]
  ring

/-- Zero point: `0 °C` (the freezing point of water) maps to `273.15 K`. -/
theorem kelvin_celsius_zero : celsiusToKelvin 0 = 273.15 := by
  simp only [celsiusToKelvin, zero_add]

end EarthScience
