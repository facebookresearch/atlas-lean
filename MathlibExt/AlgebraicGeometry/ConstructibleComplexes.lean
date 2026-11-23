/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

/-!
# Operations on constructible complexes

The coefficient sheaves, finite-rank local systems and bounded constructible
complexes with coefficients in a field `k` (`CoefficientSheaf`,
`CoefficientDerived`, `IsFiniteRankLocalSystem`, `boundedConstructible`) are
defined in `MathlibExt.AlgebraicGeometry.PerverseSheaves`, whose rational
notions are their specializations at `k = ℚ`. This module adds change of
coefficients, exact inverse image and the bounded-below derived direct image.

All carriers are actual sheaves on complex analytification. Scalar extension
is performed on presheaves and then sheafified; pointwise tensoring a sheaf
with a coefficient field need not already satisfy the sheaf condition.

The constructions below are complete. Exactness of scalar extension and the
closure and preservation properties of constructibility are requested in
`WantedExt/AlgebraicGeometry/ConstructibleComplexesWanted.lean`.

## References

* A. Dimca, *Sheaves in Topology*, Chapters 2–4.
* M. de Cataldo and L. Migliorini, https://arxiv.org/abs/0712.0349, §1.5.
* The Stacks Project, Tags 00W1 (sheafification) and 09YH (constructibility).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConstructibleComplexes

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- Scalar extension of sheaves: forget, extend coefficients, sheafify. -/
def scalarExtension (k l : Type) [Field k] [Field l] [Algebra k l] (Z : TopCat.{0}) :
    CoefficientSheaf k Z ⥤ CoefficientSheaf l Z :=
  TopCat.Sheaf.forget (ModuleCat.{0} k) Z ⋙
    (Functor.whiskeringRight (Opens Z)ᵒᵖ (ModuleCat.{0} k) (ModuleCat.{0} l)).obj
      (ModuleCat.extendScalars (algebraMap k l)) ⋙
    presheafToSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} l)

/-- Exactness of this fixed scalar-extension functor; no instance is claimed
here. Each field is an actual Mathlib preservation condition. -/
class ScalarExtensionExact (k l : Type) [Field k] [Field l] [Algebra k l]
    (Z : TopCat.{0}) : Prop where
  [additive : (scalarExtension k l Z).Additive]
  [limits : PreservesFiniteLimits (scalarExtension k l Z)]
  [colimits : PreservesFiniteColimits (scalarExtension k l Z)]

attribute [instance] ScalarExtensionExact.additive ScalarExtensionExact.limits
  ScalarExtensionExact.colimits

/-- Derived scalar extension, induced by the fixed exact sheaf functor. -/
def derivedScalarExtension (k l : Type) [Field k] [Field l] [Algebra k l]
    (Z : TopCat.{0}) [ScalarExtensionExact k l Z] :
    CoefficientDerived k Z ⥤ CoefficientDerived l Z :=
  (scalarExtension k l Z).mapDerivedCategory

/-- The ordinary inverse-image functor with the coefficient field fixed. -/
abbrev pullback (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :=
  TopCat.Sheaf.pullback (ModuleCat.{0} k) f

/-- Inverse image of sheaves preserves finite limits: Mathlib's site pullback
along the representably flat functor `Opens.map f` is left exact. -/
instance pullback_preservesFiniteLimits (k : Type) [Field k] {Z W : TopCat.{0}}
    (f : Z ⟶ W) : PreservesFiniteLimits (pullback k f) := by
  have : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits _
  have : ReflectsLimits (CategoryTheory.forget (ModuleCat.{0} k)) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens W)ᵒᵖ ⥤ ModuleCat.{0} k) ⥤
        (Opens Z)ᵒᵖ ⥤ ModuleCat.{0} k) :=
    lan_preservesFiniteLimits_of_flat (ModuleCat.{0} k) (Opens.map f)
  change PreservesFiniteLimits ((Opens.map f).sheafPullback
    (ModuleCat.{0} k) (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z))
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Inverse image of sheaves is additive, since it preserves finite products. -/
instance pullback_additive (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (pullback k f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Derived inverse image, induced by the exact inverse-image functor. -/
def derivedPullback (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :
    CoefficientDerived k W ⥤ CoefficientDerived k Z :=
  (pullback k f).mapDerivedCategory

/-- Actual bounded-below derived direct image, with its ambient inclusion. -/
def derivedPushforwardPlus (k : Type) [Field k] {X Y : ComplexScheme} (f : X ⟶ Y) :
    DerivedCategory.Plus (CoefficientSheaf k (space X)) ⥤ CoefficientDerived k (space Y) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (spaceMap f)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι

end MathlibExt.AlgebraicGeometry.ConstructibleComplexes
