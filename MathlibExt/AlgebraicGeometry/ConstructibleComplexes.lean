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
# Constructible complexes and change of coefficients

All carriers are actual sheaves on complex analytification. Scalar extension
is performed on presheaves and then sheafified; pointwise tensoring a sheaf
with a coefficient field need not already satisfy the sheaf condition.

The ordinary constructions below are complete. The exactness and geometric
preservation results are requested in the matching Wanted module. The two
imported analytification/perverse-definition cores are unchanged public code
from ATLAS PR 1970; no wanted provider is imported.

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

/-- Sheaves with coefficients in the specified field, on an actual space. -/
abbrev CoefficientSheaf (k : Type) [Field k] (Z : TopCat.{0}) :=
  TopCat.Sheaf (ModuleCat.{0} k) Z

/-- The actual derived category for the specified coefficients. -/
abbrev CoefficientDerived (k : Type) [Field k] (Z : TopCat.{0}) :=
  DerivedCategory (CoefficientSheaf k Z)

/-- Local triviality by a constant finite-dimensional coefficient module. -/
def IsFiniteRankLocalSystem (k : Type) [Field k] (Z : TopCat.{0})
    (F : CoefficientSheaf k Z) : Prop :=
  ∀ x : Z, ∃ U : Opens Z, x ∈ U ∧
    ∃ V : ModuleCat.{0} k, FiniteDimensional k V ∧
      Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (openInclusion Z U)).obj F ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of U))
          (ModuleCat.{0} k)).obj V)

/-- Bounded cohomology with a common finite smooth algebraic stratification. -/
def boundedConstructible (k : Type) [Field k] (X : ComplexScheme) :
    ObjectProperty (CoefficientDerived k (space X)) := fun K ↦
  (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j →
    IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) ∧
  ∃ S : AlgebraicStratification X, ∀ a j,
    IsFiniteRankLocalSystem k (space (S.stratum a))
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (spaceMap (S.inclusion a))).obj
        ((DerivedCategory.homologyFunctor _ j).obj K))

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

/-- Exactness of the actual inverse-image sheaf functor. -/
class PullbackExact (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) : Prop where
  [additive : (pullback k f).Additive]
  [limits : PreservesFiniteLimits (pullback k f)]
  [colimits : PreservesFiniteColimits (pullback k f)]

attribute [instance] PullbackExact.additive PullbackExact.limits PullbackExact.colimits

/-- Exactness of inverse image follows from Mathlib's representably-flat
site pullback and its left adjunction. This is a completed provider. -/
instance pullbackExact (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :
    PullbackExact k f := by
  have : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits _
  have : ReflectsLimits (CategoryTheory.forget (ModuleCat.{0} k)) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens W)ᵒᵖ ⥤ ModuleCat.{0} k) ⥤
        (Opens Z)ᵒᵖ ⥤ ModuleCat.{0} k) :=
    lan_preservesFiniteLimits_of_flat (ModuleCat.{0} k) (Opens.map f)
  have hlim : PreservesFiniteLimits (pullback k f) := by
    change PreservesFiniteLimits ((Opens.map f).sheafPullback
      (ModuleCat.{0} k) (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z))
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  have hcolim : PreservesFiniteColimits (pullback k f) := by
    change PreservesFiniteColimits (TopCat.Sheaf.pullback (ModuleCat.{0} k) f)
    infer_instance
  exact { additive := Functor.additive_of_preserves_binary_products _
          limits := hlim
          colimits := hcolim }

/-- Derived inverse image, induced by the fixed exact inverse-image functor. -/
def derivedPullback (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W)
    [PullbackExact k f] : CoefficientDerived k W ⥤ CoefficientDerived k Z :=
  (pullback k f).mapDerivedCategory

instance pushforward_additive (k : Type) [Field k] {Z W : TopCat.{0}} (f : Z ⟶ W) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).Additive where
  map_add := by intro F G a b; rfl

/-- Actual bounded-below derived direct image, with its ambient inclusion. -/
def derivedPushforwardPlus (k : Type) [Field k] {X Y : ComplexScheme} (f : X ⟶ Y) :
    DerivedCategory.Plus (CoefficientSheaf k (space X)) ⥤ CoefficientDerived k (space Y) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (spaceMap f)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι

end MathlibExt.AlgebraicGeometry.ConstructibleComplexes
