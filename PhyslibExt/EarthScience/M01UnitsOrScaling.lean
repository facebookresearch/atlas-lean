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
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Unit-scale conversions and affine temperature scales

Unit conversions for magnitudes of one dimension are multiplications
by strictly positive scales, and temperature differences transform linearly
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
- `EarthScience.kelvin_celsius_zero`: `0 °C` maps to `273.15 K`.
- `EarthScience.unitConversionLinearEquiv` and
  `EarthScience.celsiusToKelvinAffineEquiv`: bundled conversions for the
  standard linear and affine inverse and composition APIs.

## iii. Table of contents

- A. Unit-scale conversions
- B. Temperature differences, affine map, and zero point

## iv. References

- BIPM, *A concise summary of the International System of Units, SI*,
  paragraph following Table 2: `t/°C = T/K - 273.15`.
  <https://www.bipm.org/documents/d/guest/si-brochure-9-concise-en?download=true>
- Mathlib's `LinearEquiv.smulOfUnit` and `AffineEquiv.vaddConst`.
  No Physlib dimension API is used: these are real coordinate conversions.

## A. Unit-scale conversions
-/

@[expose] public section

namespace EarthScience

/-- Unit-scale conversion by a strictly positive scale `a`: `C_a(x) = a * x`.
Scales are units of `NNReal`, so strict positivity is carried by the
type and the scale `0` is excluded. -/
def unitConversion (a : NNRealˣ) (x : ℝ) : ℝ := (a : ℝ) * x

/-- A positive unit-scale conversion as an invertible real linear map. -/
noncomputable def unitConversionLinearEquiv (a : NNRealˣ) : ℝ ≃ₗ[ℝ] ℝ :=
  LinearEquiv.smulOfUnit (Units.map NNReal.toRealHom.toMonoidHom a)

/-- The bundled linear map agrees with unit-scale conversion. -/
@[simp]
lemma unitConversionLinearEquiv_apply (a : NNRealˣ) (x : ℝ) :
    unitConversionLinearEquiv a x = unitConversion a x := rfl

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

/-- Celsius-to-Kelvin conversion as an affine equivalence of real coordinates. -/
noncomputable def celsiusToKelvinAffineEquiv : ℝ ≃ᵃ[ℝ] ℝ :=
  AffineEquiv.vaddConst ℝ (273.15 : ℝ)

/-- The bundled affine map agrees with Celsius-to-Kelvin conversion. -/
@[simp]
lemma celsiusToKelvinAffineEquiv_apply (C : ℝ) :
    celsiusToKelvinAffineEquiv C = celsiusToKelvin C := rfl

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

/-- Zero point: `0 °C` maps to `273.15 K`. -/
theorem kelvin_celsius_zero : celsiusToKelvin 0 = 273.15 := by
  simp only [celsiusToKelvin, zero_add]

end EarthScience
