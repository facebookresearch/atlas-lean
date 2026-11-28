/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.LocalizationAway
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-! Tests for `MathlibExt.RingTheory.DiscreteValuationRing.LocalizationAway`. -/

#check @IsDiscreteValuationRing.isLocalization_away_of_irreducible

/-- `ℚ_[p]` is the localization of `ℤ_[p]` away from `p`. -/
example (p : ℕ) [Fact p.Prime] : IsLocalization.Away (p : ℤ_[p]) ℚ_[p] :=
  IsDiscreteValuationRing.isLocalization_away_of_irreducible ℚ_[p] PadicInt.irreducible_p
