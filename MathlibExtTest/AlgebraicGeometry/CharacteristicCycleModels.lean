/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CharacteristicCycleModels
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.ZMod

/-!
Source convention regressions: Theorem 4.9 allows 1/2 in characteristic 2
but its initial characteristic-zero coefficients are integers; the
cohomological alternating sign must also agree in negative degrees.
These checks construct no characteristic cycle or vanishing representation.
-/

open MathlibExt.AlgebraicGeometry.CharacteristicCycleModels

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example (a : ℚ) : IsLocalizedInteger ℚ a ↔ ∃ m : ℤ, a = (m : ℚ) := by
  simp [IsLocalizedInteger, coefficientDenominator]

example : IsLocalizedInteger (ZMod 2) (1 / 2 : ℚ) := by
  refine ⟨1, 1, ?_⟩
  norm_num [coefficientDenominator, ZMod.ringChar_zmod_n]

example : ¬IsLocalizedInteger ℚ (1 / 2 : ℚ) := by
  simp only [IsLocalizedInteger, coefficientDenominator, ringChar.eq_zero, ite_true,
    Nat.cast_one, one_pow, mul_one]
  rintro ⟨m, r, h⟩
  have denominator := congrArg Rat.den h
  norm_num at denominator

example (q : ℤ) : (-1 : ℚ) ^ q.natAbs = (-1 : ℚ) ^ q := by
  cases q with
  | ofNat n => simp
  | negSucc n => simp [pow_succ, ← inv_pow]

#check MathlibExt.AlgebraicGeometry.EtaleMilnorConductorModels.MilnorComparison.operator_intertwines
#check
  MathlibExt.AlgebraicGeometry.EtaleMilnorConductorModels.MilnorComparison.reduction_intertwines
