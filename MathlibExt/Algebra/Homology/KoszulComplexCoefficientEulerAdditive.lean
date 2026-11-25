/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientExact
public import MathlibExt.Algebra.Homology.FiniteLengthEulerAdditive

/-!
# Euler additivity for Koszul complexes with coefficients

The terms of a finite-family Koszul complex are free, so tensoring preserves
short exact coefficient sequences. The homology long exact sequence then
gives additivity of the associated finite-length Euler characteristics.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The original Koszul tensor Euler invariant is additive on
actual short exact coefficient modules with their finite homology data. -/
theorem familyTensorCoefficientEuler_shortExact
    (a : Fin n → R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (h₁ : HomologicalComplex.FiniteLengthHomologyData R
      (familyTensorCoefficientComplex R a S.X₁))
    (h₂ : HomologicalComplex.FiniteLengthHomologyData R
      (familyTensorCoefficientComplex R a S.X₂))
    (h₃ : HomologicalComplex.FiniteLengthHomologyData R
      (familyTensorCoefficientComplex R a S.X₃)) :
    HomologicalComplex.finiteLengthEulerCharacteristic R h₂ =
      HomologicalComplex.finiteLengthEulerCharacteristic R h₁ +
        HomologicalComplex.finiteLengthEulerCharacteristic R h₃ :=
  HomologicalComplex.finiteLengthEulerCharacteristic_shortExact
    (familyTensorCoefficientShortComplex R a S)
    (familyTensorCoefficientShortComplex_shortExact R a S hS) h₁ h₂ h₃

end KoszulComplex
