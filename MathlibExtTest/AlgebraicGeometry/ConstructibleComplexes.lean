/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.ConstructibleComplexes` -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes

namespace MathlibExtTest.AlgebraicGeometry.ConstructibleComplexes

attribute [local instance] HasDerivedCategory.standard

variable (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W)

/-- Inverse image is exact, for every continuous map and coefficient field. -/
example : PreservesFiniteLimits (pullback k f) := inferInstance
example : PreservesFiniteColimits (pullback k f) := inferInstance
example : (pullback k f).Additive := inferInstance

/-- Derived inverse image needs no exactness hypothesis. -/
example : CoefficientDerived k W ⥤ CoefficientDerived k Z := derivedPullback k f

/-- Derived inverse image is the derived functor of the exact inverse image. -/
example : derivedPullback k f = (pullback k f).mapDerivedCategory := rfl

/-- Derived inverse image on rational complexes. -/
example : RationalDerived W ⥤ RationalDerived Z := derivedPullback ℚ f

/-- Scalar extension of sheaves is exact, for every field extension and space,
so derived scalar extension needs no hypothesis. -/
example (l : Type) [Field l] [Algebra k l] :
    PreservesFiniteLimits (scalarExtension k l Z) := inferInstance
example (l : Type) [Field l] [Algebra k l] :
    PreservesFiniteColimits (scalarExtension k l Z) := inferInstance
example (l : Type) [Field l] [Algebra k l] : (scalarExtension k l Z).Additive :=
  inferInstance
example (l : Type) [Field l] [Algebra k l] :
    CoefficientDerived k Z ⥤ CoefficientDerived l Z :=
  derivedScalarExtension k l Z

/-- Scalar extension extends coefficients objectwise and then sheafifies. -/
example (l : Type) [Field l] [Algebra k l] :
    scalarExtension k l Z =
      TopCat.Sheaf.forget (ModuleCat.{0} k) Z ⋙
        (Functor.whiskeringRight (Opens Z)ᵒᵖ (ModuleCat.{0} k) (ModuleCat.{0} l)).obj
          (ModuleCat.extendScalars (algebraMap k l)) ⋙
        presheafToSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} l) :=
  rfl

/-- Extension of scalars of modules along a field extension is left exact. -/
example (l : Type) [Field l] [Algebra k l] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{0, 0, 0} (algebraMap k l)) :=
  inferInstance

/-- Bounded-below derived direct image along an algebraic morphism. -/
example {X Y : ComplexScheme} (g : X ⟶ Y) :
    DerivedCategory.Plus (CoefficientSheaf k (space X)) ⥤ CoefficientDerived k (space Y) :=
  derivedPushforwardPlus k g

/-- The normalized direct image is the derived direct image of the constant
sheaf placed in degree `-n`. -/
example {X Y : ComplexScheme} (g : X ⟶ Y) (n : ℕ) :
    normalizedDirectImage k X Y g n =
      DerivedCategory.Plus.ι.obj
        (((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (spaceMap g)).rightDerivedFunctorPlus).obj
          ((DerivedCategory.Plus.singleFunctor (CoefficientSheaf k (space X)) (-(n : ℤ))).obj
            ((constantSheaf (Opens.grothendieckTopology (space X)) (ModuleCat.{0} k)).obj
              (ModuleCat.of k k)))) :=
  rfl

/-- The constant sheaf of a finite-dimensional space is a finite-rank local
system, for any coefficient field. -/
example (V : ModuleCat.{0} k) [FiniteDimensional k V] :
    IsFiniteRankLocalSystem k Z
      ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj V) :=
  isFiniteRankLocalSystem_constantSheaf k Z V

end MathlibExtTest.AlgebraicGeometry.ConstructibleComplexes

end
