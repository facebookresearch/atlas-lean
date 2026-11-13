/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Real.Basic
public import PhyslibExt.Units.QuantityDimensions

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
/-!
# Arrhenius law is increasing in temperature

An admissible Arrhenius law `k(T) = A * exp(-(Ea / (R * T)))`, with a typed prefactor
`A > 0`, molar activation energy `Ea`, gas constant `R > 0` and absolute temperature
`T > 0`, is positive, and for `Ea > 0` it is strictly increasing in `T`.

## i. Overview

The exponential factor is `Units.QuantityDimensions.expScaledEnergy Ea R T`: `Ea` is a molar
energy, `R` a gas constant and `T` an absolute temperature, each a typed `WithDim` quantity,
so the exponent `Ea / (R * T)` is dimensionless by construction and unchanged by a change of
units. The prefactor `A` is a `WithDim d ℝ` quantity of an arbitrary dimension `d` (the
dimension of a rate constant depends on the reaction order); the rate is the coordinate
`A.val * expScaledEnergy Ea R T`.

As `T` grows, `R * T` grows, so `Ea / (R * T)` falls, `-(Ea / (R * T))` rises, and `exp`
preserves the order; multiplying by `A > 0` preserves it again. Positive activation energy
is essential: at `Ea = 0` the law is constant. The raw-coordinate argument is a private
lemma, reached through `expScaledEnergy_val`.

## ii. Key results

- `EarthScience.arrhenius_pos`: `k(T) > 0`.
- `EarthScience.arrhenius_strictMono`: `k` is strictly increasing on positive absolute
  temperatures for `Ea > 0`.

## iii. References

- `Units.QuantityDimensions.expScaledEnergy`, `Units.QuantityDimensions.expScaledEnergy_val`.
- `Real.exp_pos`, `Real.exp_strictMono`, `div_lt_div_of_pos_left`,
  `mul_lt_mul_of_pos_left` in Mathlib.
-/

@[expose] public section

open Units.QuantityDimensions

namespace EarthScience

/-- Coordinate form of the monotonicity step: for `A > 0`, `Ea > 0`, `R > 0` and
`0 < x < y`, `A * exp(-(Ea / (R * x))) < A * exp(-(Ea / (R * y)))`. -/
private lemma arrhenius_coord_lt {A Ea R x y : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R)
    (hx : 0 < x) (hxy : x < y) :
    A * Real.exp (-(Ea / (R * x))) < A * Real.exp (-(Ea / (R * y))) := by
  have hRx : 0 < R * x := mul_pos hR hx
  have hRxy : R * x < R * y := mul_lt_mul_of_pos_left hxy hR
  have hE : Ea / (R * y) < Ea / (R * x) := div_lt_div_of_pos_left hEa hRx hRxy
  exact mul_lt_mul_of_pos_left (Real.exp_strictMono (neg_lt_neg hE)) hA

/-- An admissible Arrhenius law `k(T) = A * exp(-(Ea / (R * T)))`, with a typed prefactor
`A > 0`, a molar activation energy `Ea`, a gas constant `R > 0` and an absolute temperature
`T > 0`, is positive. -/
theorem arrhenius_pos {d : Dimension ISQDimensionBase} {A : WithDim d ℝ} (hA : 0 < A.val)
    (Ea : WithDim molarEnergyDim ℝ) {R : WithDim gasConstantDim ℝ}
    {T : WithDim temperatureDim ℝ} (hR : 0 < R.val) (hT : 0 < T.val) :
    0 < A.val * expScaledEnergy Ea R T hR hT := by
  rw [expScaledEnergy_val]
  exact mul_pos hA (Real.exp_pos _)

/-- An admissible Arrhenius law is strictly increasing in the absolute temperature: for a
typed prefactor `A > 0`, a molar activation energy `Ea > 0` and a gas constant `R > 0`, the
rate `T ↦ A * exp(-(Ea / (R * T)))` is strictly monotone on temperatures `T > 0`. -/
theorem arrhenius_strictMono {d : Dimension ISQDimensionBase} {A : WithDim d ℝ}
    (hA : 0 < A.val) {Ea : WithDim molarEnergyDim ℝ} (hEa : 0 < Ea.val)
    {R : WithDim gasConstantDim ℝ} (hR : 0 < R.val) :
    StrictMono fun T : {T : WithDim temperatureDim ℝ // 0 < T.val} =>
      A.val * expScaledEnergy Ea R T.1 hR T.2 := by
  intro T₁ T₂ h
  simp only [expScaledEnergy_val]
  exact arrhenius_coord_lt hA hEa hR T₁.2 h

end EarthScience
