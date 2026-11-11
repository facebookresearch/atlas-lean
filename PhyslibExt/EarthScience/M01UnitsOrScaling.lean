/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Unit-scale conversions and affine temperature scales

Unit conversions for magnitudes of one dimension are multiplications
by positive scales, and temperature differences transform linearly
while absolute Celsius-to-Kelvin conversion is affine.

## i. Overview

A conversion `C_a` sends a scalar `x` to `a * x` for a positive scale
`a`. Converting by `a` and then by `b` is converting by the composite
scale `b * a`, which stays positive. Kelvin and Celsius are related by
`T_K = T_C + 273.15`: a temperature difference `Δ` in Celsius is the
same difference in kelvin, while an absolute temperature shifts by
the `273.15` offset. No new dimensions type is introduced; the
statements are real algebra on the existing carriers.

## ii. Key results

- `EarthScience.unit_conversion_comp`: conversions compose, and the
  composite scale stays positive.
- `EarthScience.kelvin_celsius_difference`: Kelvin differences equal
  Celsius differences.
- `EarthScience.kelvin_celsius_affine`: the Celsius-to-Kelvin map
  preserves affine combinations, with `0 °C` (the freezing point of water) mapping to `273.15 K`.

## iii. Table of contents

- A. Composition of unit-scale conversions
- B. Temperature differences and the affine Kelvin map

## iv. References

- `mul_pos` and `ring` (Mathlib), which close all three proofs.
  No Physlib dimension API is used: the milestone is the real
  algebra of scales and offsets, not a new quantity base.

## A. Composition of unit-scale conversions
-/

@[expose] public section

namespace EarthScience

/-- Unit-scale conversions compose: converting by `a` then by `b` is
converting by `b * a`, and the composite scale stays positive. -/
theorem unit_conversion_comp {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b * (a * x) = (b * a) * x ∧ 0 < b * a := by
  exact ⟨by ring, mul_pos hb ha⟩

/-! ## B. Temperature differences and the affine Kelvin map -/

/-- Temperature differences transform linearly: the Kelvin value of
`C + Δ` minus the Kelvin value of `C` is exactly `Δ`. -/
theorem kelvin_celsius_difference {C Δ : ℝ} :
    (C + Δ + 273.15) - (C + 273.15) = Δ := by
  ring

/-- The Celsius-to-Kelvin map `C ↦ C + 273.15` is affine: it preserves
affine combinations, and `0 °C` maps to `273.15 K`. -/
theorem kelvin_celsius_affine {C₁ C₂ α : ℝ} :
    (α * C₁ + (1 - α) * C₂ + 273.15)
      = α * (C₁ + 273.15) + (1 - α) * (C₂ + 273.15) ∧ (0 + 273.15 : ℝ) = 273.15 := by
  exact ⟨by ring, zero_add _⟩

end EarthScience
