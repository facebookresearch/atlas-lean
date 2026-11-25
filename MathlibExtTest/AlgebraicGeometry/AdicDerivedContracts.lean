/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AdicDerivedContracts
import MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules

/-! # Tests for linear pullback, continuous coefficient rings and adic derived functors

The cohomology pullback is linear over the coefficient ring; constants act through constant
functions; the underlying module of the unit is the continuous coefficient sheaf, by the identity
on sections; single complexes and maps behave as stated; the vanishing object is a bounded-below
complex.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AdicDerivedContracts

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
open MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules
open MathlibExt.AlgebraicGeometry.AdicDerivedContracts

section Linear

variable (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X)

/-- The cohomology pullback commutes with scalars. -/
example {F : CoefficientSheaf X R} {G : CoefficientSheaf Y R} (c : (pullback R f).obj F ⟶ G)
    (n : ℕ) (r : R) (a : Cohomology R X F n) :
    cohomologyPullback R f c n (r • a) = r • cohomologyPullback R f c n a := by
  rw [← cohomologyPullbackLinear_apply, map_smul, cohomologyPullbackLinear_apply]

example : Functor.Linear R (pullback R f) := inferInstance

end Linear

section CoefficientRing

variable (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] (X : Scheme.{0})

/-- Constants act through constant functions. -/
example (a : E) (x : (⊤_ X.ProEt).left) :
    (show C((⊤_ X.ProEt).left, ULift.{1} E) from constantScalars E X a) x = ULift.up a := rfl

/-- The underlying module of the unit is the continuous coefficient sheaf, by the identity. -/
example (U : X.ProEtᵒᵖ) (a : C(U.unop.left, ULift.{1} E)) :
    (unitUnderlyingIso E X).hom.hom.app U a = a := rfl

example : (underlying E X).Additive := inferInstance

end CoefficientRing

section Derived

variable (R : Type) [CommRing R]

attribute [local instance] HasDerivedCategory.standard

example {X : Scheme.{0}} {F G : ModuleSheaf R X} (a : F ⟶ G) [IsIso a] :
    IsIso (singleMap R a) := inferInstance

/-- Inverse image is exact, so its derived unit is an isomorphism, unconditionally. -/
example {Y X : Scheme.{0}} (f : Y ⟶ X) (K : Cochains R X) :
    IsIso ((pullback R f).rightDerivedFunctorPlusUnit.app K) := inferInstance

example {Y X : Scheme.{0}} (f : Y ⟶ X) (A : ModuleSheaf R X) :
    IsIso (pullbackUnitOfSheaf R f A) := inferInstance

example {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback R g ⋙ pullback R f ≅ pullback R (f ≫ g) := pullbackComp R f g

/-- Derived inverse images compose, compatibly with the composition on complexes. -/
example {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (K : Cochains R Z) :
    compositePullbackUnit R f g K ≫
        (DerivedPullbackPasting.comparison (R := R) (f := f) (g := g)).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.Plus.Q.mapIso (cochainPullbackComp R f g K)).hom ≫
        (pullback R (f ≫ g)).rightDerivedFunctorPlusUnit.app K :=
  DerivedPullbackPasting.normalized K

/-- Global sections are Mathlib's evaluation at the terminal object. -/
example (X : Scheme.{0}) :
    sections R X = (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{1} R)).obj
      (op (⊤_ X.ProEt)) := rfl

example {Y X : Scheme.{0}} (f : Y ⟶ X) :
    pushforward R f ⋙ sections R X ≅ sections R Y := sectionsPushforward R f

/-- The vanishing object is an object of the bounded-below derived category. -/
example (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] {A Y Z : Scheme.{0}} {j : Y ⟶ A}
    {i : Z ⟶ A} [PullbackDerivedNormalization R i] [IsIso (coefficientPullback R M i)]
    (V : VanishingCochainModel R M j i) : Derived R Z :=
  vanishingObject R M V

end Derived

end MathlibExtTest.AlgebraicGeometry.AdicDerivedContracts
