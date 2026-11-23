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

/-- Derived scalar extension uses the requested exactness of scalar extension. -/
example (l : Type) [Field l] [Algebra k l] [ScalarExtensionExact k l Z] :
    CoefficientDerived k Z ⥤ CoefficientDerived l Z :=
  derivedScalarExtension k l Z

/-- Bounded-below derived direct image along an algebraic morphism. -/
example {X Y : ComplexScheme} (g : X ⟶ Y) :
    DerivedCategory.Plus (CoefficientSheaf k (space X)) ⥤ CoefficientDerived k (space Y) :=
  derivedPushforwardPlus k g

/-- The constant sheaf of a finite-dimensional space is a finite-rank local
system, for any coefficient field. -/
example (V : ModuleCat.{0} k) [FiniteDimensional k V] :
    IsFiniteRankLocalSystem k Z
      ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj V) :=
  isFiniteRankLocalSystem_constantSheaf k Z V

end MathlibExtTest.AlgebraicGeometry.ConstructibleComplexes

end
