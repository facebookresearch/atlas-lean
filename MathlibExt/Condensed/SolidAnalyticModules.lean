/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Condensed.Solid
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import MathlibExt.Condensed.GeometricScalarRestriction

/-!
# Correct local solid analytic tests on actual topological coefficients

The topological coefficient ring is C(-,A), and its modules are actual
module sheaves. Solid tests use the native free-to-right-Kan maps only
for the finite-type integer rings Z and Z[T]. Every scalar test restricts
through the actual constant continuous coefficient map. The known
incorrect general-R shortcut in Mathlib's Solid file is never used on A.

An analytic reflection is characterized by the actual tests and its
unit-precomposition universal property. The free profinite measuring
objects are the actual presheaf-free/sheafified representables. Derived
adic completion, completed compact DG models and geometric v-descent
are separate companions; no ordinary Ind of a homotopy category is used.

References: Clausen--Scholze, condensed mathematics Lecture V;
Anschuetz--Mann, arXiv:2403.01951v2, Section2.1 and Definition2.4.
-/

@[expose] public noncomputable section

namespace MathlibExt.Condensed.SolidAnalyticModules

open CategoryTheory CategoryTheory.Limits Opposite
open GeometricScalarRestriction TopologicalRings

attribute [local instance] HasDerivedCategory.standard

variable (A : Type 1) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

abbrev GeometricDerived := DerivedCategory (GeometricModules A)

/-- The actual coefficient unit, in degree zero. -/
abbrev unitObject : GeometricDerived A :=
  (DerivedCategory.singleFunctor (GeometricModules A) 0).obj
    (SheafOfModules.unit (ringSheaf A))

abbrev Integers := ULift.{1} ℤ
abbrev IntegerPolynomial := ULift.{1} (Polynomial ℤ)

/-- The prescribed integer scalar map into the actual topological ring. -/
def integerScalars : Integers →+* A :=
  (Int.castRingHom A).comp ULift.ringEquiv.toRingHom

/-- The actual polynomial scalar map with T sent to the specified element. -/
def polynomialScalars (a : A) : IntegerPolynomial →+* A :=
  (Polynomial.eval₂RingHom (Int.castRingHom A) a).comp ULift.ringEquiv.toRingHom

/-- The literal native solidification test, in all shifted Hom groups.
It is used as derived solidity only for the finite-type integer scalars below;
no assertion of correct general-ring solidity is made. -/
def solidificationTest (R : Type 1) [CommRing R]
    (K : DerivedCategory (CondensedMod.{0} R)) : Prop :=
  ∀ (S : Profinite.{0}) (n : ℤ), Function.Bijective
    (fun f : ((DerivedCategory.singleFunctor (CondensedMod.{0} R) 0).obj
      ((_root_.Condensed.profiniteSolid R).obj S))⟦n⟧ ⟶ K ↦
        (shiftFunctor (DerivedCategory (CondensedMod.{0} R)) n).map
          ((DerivedCategory.singleFunctor (CondensedMod.{0} R) 0).map
            ((_root_.Condensed.profiniteSolidification R).app S)) ≫ f)

/-- Correct integer derived-solid coefficients. -/
abbrev IsIntegerSolid (K : DerivedCategory (CondensedMod.{0} Integers)) : Prop :=
  solidificationTest Integers K

/-- Correct finite-type integer-polynomial derived-solid coefficients. -/
abbrev IsPolynomialSolid (K : DerivedCategory (CondensedMod.{0} IntegerPolynomial)) :
    Prop := solidificationTest IntegerPolynomial K

/-- Fixed ordinary derived-source input for every prescribed scalar map. -/
structure RestrictionInput (S : Subring A) where
  integer : HasDerivedRestriction A Integers (integerScalars A)
  polynomial : ∀ a : S,
    HasDerivedRestriction A IntegerPolynomial (polynomialScalars A a)

/-- The genuine Z-solid and elementwise Z[T]-analytic completeness test. -/
def IsAnalyticComplete (S : Subring A) (E : RestrictionInput A S)
    (K : GeometricDerived A) : Prop :=
  letI := E.integer
  IsIntegerSolid ((derivedRestriction A Integers (integerScalars A)).obj K) ∧
    ∀ a : S,
      letI := E.polynomial a
      IsPolynomialSolid
        ((derivedRestriction A IntegerPolynomial (polynomialScalars A a)).obj K)

/-- The actual analytic localization reflector, with its fixed unit. -/
structure AnalyticReflection (S : Subring A) (E : RestrictionInput A S) where
  functor : GeometricDerived A ⥤ GeometricDerived A
  unit : 𝟭 (GeometricDerived A) ⟶ functor
  complete : ∀ K, IsAnalyticComplete A S E (functor.obj K)
  universal : ∀ (K L : GeometricDerived A), IsAnalyticComplete A S E L →
    Function.Bijective (fun f : functor.obj K ⟶ L ↦ unit.app K ≫ f)

/-- The real free A-module on the condensed profinite representable S. -/
def freeProfinite (S : Profinite.{0}) : GeometricModules A :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf A).obj)).obj
    (PresheafOfModules.freeObj
      (R := (ringSheaf A).obj) (profiniteToCondensed.obj S).obj)

/-- The actual free measuring object in the native derived category. -/
def freeProfiniteObject (S : Profinite.{0}) : GeometricDerived A :=
  (DerivedCategory.singleFunctor (GeometricModules A) 0).obj (freeProfinite A S)

/-- Analytic generators are the prescribed reflection of the actual free objects. -/
def analyticGenerator (S : Subring A) (E : RestrictionInput A S)
    (L : AnalyticReflection A S E) (T : Profinite.{0}) : GeometricDerived A :=
  L.functor.obj (freeProfiniteObject A T)

end MathlibExt.Condensed.SolidAnalyticModules
