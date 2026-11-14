/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
public import MathlibExt.AlgebraicGeometry.BettiFunctoriality
/-!
# Proper cohomological Gysin maps from actual Borel--Moore duality

For smooth pure-dimensional spaces with specified dualizing purities, Poincaré
identification is an actual linear equivalence between derived Hom groups.
The cohomological pushforward is the already constructed proper Borel--Moore
pushforward under those two identifications. Its degree is exactly the
real dimension difference. No chosen Gysin linear map is supplied.

The geometrically compatible choice of purities, including excess and bundle
normalizations, is a separate mathematical construction. References: Fulton,
*Intersection Theory*, §19.1; Kashiwara--Schapira, Chapter III.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.BettiGysin
open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.CompactSupportBetti
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open MathlibExt.AlgebraicGeometry.BettiFunctoriality
attribute [local instance] HasDerivedCategory.standard

/-- The actual coefficient-unit class in degree zero. -/
def unitClass (Z : TopCat.{0}) : BettiRealization.Cohomology Z 0 :=
  (shiftFunctorZero (RationalDerived Z) ℤ).inv.app (rationalUnit Z)

/-- A selected smooth purity family. Compatibility with geometric operations
is a separate mathematical condition, not asserted by this data structure. -/
structure PureFamily
    (D : ∀ (X : ComplexScheme) [IsComplexVariety X],
      DualizingComplex (ComplexAnalytification.space X)) where
  iso : ∀ (X : ComplexScheme) [IsComplexVariety X] (d : ℕ)
    [_root_.AlgebraicGeometry.SmoothOfRelativeDimension d X.hom],
    (D X).obj ≅ (rationalUnit (ComplexAnalytification.space X))⟦(2 * d : ℤ)⟧

def purityHomologyIso (Z : TopCat.{0}) (D : DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (rationalUnit Z)⟦(2 * d : ℤ)⟧) (m : ℤ) :
    D.obj⟦-m⟧ ≅ (rationalUnit Z)⟦(2 * d : ℤ)-m⟧ :=
  (shiftFunctor (RationalDerived Z) (-m)).mapIso e ≪≫
    (shiftFunctorAdd' (RationalDerived Z) (2 * d : ℤ) (-m) ((2 * d : ℤ)-m)
      (by omega)).symm.app (rationalUnit Z)

def purityHomologyEquiv (Z : TopCat.{0}) (D : DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (rationalUnit Z)⟦(2 * d : ℤ)⟧) (m : ℤ) :
    BorelMoore Z D m ≃ₗ[ℚ] BettiRealization.Cohomology Z ((2 * d : ℤ)-m) where
  toFun a := a ≫ (purityHomologyIso Z D d e m).hom
  invFun a := a ≫ (purityHomologyIso Z D d e m).inv
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp [Preadditive.add_comp]
  map_smul' r a := by simp [Linear.smul_comp]

def purityCohomologyEquiv (Z : TopCat.{0}) (D : DualizingComplex Z) (d : ℕ)
    (e : D.obj ≅ (rationalUnit Z)⟦(2 * d : ℤ)⟧) (n : ℤ) :
    BorelMoore Z D ((2 * d : ℤ)-n) ≃ₗ[ℚ] BettiRealization.Cohomology Z n := by
  let a : D.obj⟦-((2 * d : ℤ)-n)⟧ ≅ (rationalUnit Z)⟦n⟧ :=
    (shiftFunctor (RationalDerived Z) (-((2 * d : ℤ)-n))).mapIso e ≪≫
      (shiftFunctorAdd' (RationalDerived Z) (2 * d : ℤ) (-((2 * d : ℤ)-n)) n
        (by omega)).symm.app (rationalUnit Z)
  exact { toFun := fun x => x ≫ a.hom
          invFun := fun x => x ≫ a.inv
          left_inv := by intro x; simp
          right_inv := by intro x; simp
          map_add' := by intro x y; simp [Preadditive.add_comp]
          map_smul' := by intro r x; simp [Linear.smul_comp] }

def cohomologyPushforward {Z W : TopCat.{0}} {f : Z ⟶ W}
    (P : ProperPullback f) (DZ : DualizingComplex Z) (DW : DualizingComplex W)
    (dZ dW : ℕ) (eZ : DZ.obj ≅ (rationalUnit Z)⟦(2 * dZ : ℤ)⟧)
    (eW : DW.obj ≅ (rationalUnit W)⟦(2 * dW : ℤ)⟧) (n : ℤ) :
    BettiRealization.Cohomology Z n →ₗ[ℚ]
      BettiRealization.Cohomology W ((2 * dW : ℤ)-((2 * dZ : ℤ)-n)) :=
  (purityHomologyEquiv W DW dW eW ((2 * dZ : ℤ)-n)).toLinearMap ∘ₗ
    borelMoorePushforward P DZ DW ((2 * dZ : ℤ)-n) ∘ₗ
      (purityCohomologyEquiv Z DZ dZ eZ n).symm.toLinearMap

end MathlibExt.AlgebraicGeometry.BettiGysin
