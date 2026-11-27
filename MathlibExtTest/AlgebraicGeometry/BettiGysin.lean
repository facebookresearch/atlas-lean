/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BettiGysin

@[expose] public section

/-! # Tests for the unit class, Poincaré duality and Gysin maps -/

noncomputable section

open CategoryTheory
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open MathlibExt.AlgebraicGeometry.BettiGysin

namespace MathlibExtTest.AlgebraicGeometry.BettiGysin

attribute [local instance] HasDerivedCategory.standard

/-- The unit class in degree zero is the identity of the coefficient unit, up
to the zero shift. -/
example (Z : TopCat.{0}) :
    unitClass Z = (shiftFunctorZero (RationalDerived Z) ℤ).inv.app (rationalUnit Z) :=
  rfl

/-- Poincaré duality from a purity isomorphism is a linear equivalence. -/
example (Z : TopCat.{0})
    (D : MathlibExt.AlgebraicGeometry.CompactSupportBetti.DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (rationalUnit Z)⟦(2 * d : ℤ)⟧) (n : ℤ) (x : Cohomology Z n) :
    purityCohomologyEquiv Z D d e n ((purityCohomologyEquiv Z D d e n).symm x) = x :=
  (purityCohomologyEquiv Z D d e n).apply_symm_apply x

/-- Powers of a degree-two class: `h⁰` is the unit and `hʲ⁺¹` is `h ∪ hʲ`. -/
example (Z : TopCat.{0}) (h : Cohomology Z 2) : powerClass Z h 0 = unitClass Z := rfl

example (Z : TopCat.{0}) (h : Cohomology Z 2) (j : ℕ) :
    powerClass Z h (j + 1) =
      cohomologyCast (m := 2 + 2 * (j : ℤ)) (n := 2 * ((j + 1 : ℕ) : ℤ)) (by omega)
        (cup Z h (powerClass Z h j)) :=
  rfl

/-- The Gysin map of a proper map raises degrees by twice the dimension
difference. -/
example {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback f)
    (DZ : MathlibExt.AlgebraicGeometry.CompactSupportBetti.DualizingComplex Z)
    (DW : MathlibExt.AlgebraicGeometry.CompactSupportBetti.DualizingComplex W)
    (dZ dW : ℕ) (eZ : DZ.obj ≅ (rationalUnit Z)⟦(2 * dZ : ℤ)⟧)
    (eW : DW.obj ≅ (rationalUnit W)⟦(2 * dW : ℤ)⟧) (n : ℤ) :
    Cohomology Z n →ₗ[ℚ] Cohomology W ((2 * dW : ℤ) - ((2 * dZ : ℤ) - n)) :=
  cohomologyPushforward P DZ DW dZ dW eZ eW n

end MathlibExtTest.AlgebraicGeometry.BettiGysin

end
