/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityMappingSpaceMaps

/-!
# Actual small stable Verdier cofibers and their exact quotient maps

A quotient is the cofiber of the specified full exact inclusion in the
category of small stable infinity categories. Its universal property is
the equivalence of the full exact-functor categories, including every
higher natural transformation, with functors annihilating that inclusion.
No K-theory localization equivalence is used to define the quotient.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Section 5.1,
Definitions 5.4 and 5.12 and Proposition 5.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.BGTVerdierQuotients

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityCategoryModels StableInfinitySFunctorMaps
open StableInfinityMappingSpaceMaps
open scoped Simplicial

universe u

/-- A full stable subcategory uses the actual exact inclusion and full Hom test. -/
structure FullStableInclusion (A B : StableInfinityCategory.{u}) where
  functor : ExactFunctor A B
  full : IsFullyFaithful functor.map

/-- A functor annihilates the specified subcategory on the actual source objects. -/
def KillsSubcategory {A B : StableInfinityCategory.{u}}
    (i : FullStableInclusion A B) (D : StableInfinityCategory.{u})
    (a : (mapping B.toSSet D.toSSet) _⦋0⦌) : Prop :=
  IsExact B D ((mappingZero _ _).symm a) ∧
    ∀ x : A.toSSet _⦋0⦌, IsZeroObject D.toSSet
      (((mappingZero _ _).symm a).app (op ⦋0⦌)
        (i.functor.map.app (op ⦋0⦌) x))

/-- The native full infinity category of exact functors killing A. -/
def killingFunctorCategory {A B : StableInfinityCategory.{u}}
    (i : FullStableInclusion A B) (D : StableInfinityCategory.{u}) : SSet.{u} :=
  ((mapping B.toSSet D.toSSet).fullEnhancedSubcategory
    (KillsSubcategory i D)).toSSet

/-- The Verdier quotient is normalized by its entire exact-functor universal map. -/
structure StableVerdierQuotient {A B : StableInfinityCategory.{u}}
    (i : FullStableInclusion A B) where
  category : StableInfinityCategory.{u}
  quotient : ExactFunctor B category
  kills : ∀ x : A.toSSet _⦋0⦌, IsZeroObject category.toSSet
    (quotient.map.app (op ⦋0⦌) (i.functor.map.app (op ⦋0⦌) x))
  universal : ∀ D : StableInfinityCategory.{u},
    ∃ f : exactFunctorCategory category D ⟶ killingFunctorCategory i D,
      f ≫ (SSet.Subcomplex.ι _) =
        ((mapping category.toSSet D.toSSet).fullEnhancedSubcategory
          (IsExactVertex category D)).ι ≫ precomposition quotient.map D.toSSet ∧
      CategoricalWeakEquivalence f

/-- The exact sequence retains the actual source inclusion and Verdier cofiber. -/
structure StableExactSequence where
  left : StableInfinityCategory.{u}
  middle : StableInfinityCategory.{u}
  inclusion : FullStableInclusion left middle
  quotient : StableVerdierQuotient inclusion

/-- Its third category is the actual quotient constructed from that inclusion. -/
def StableExactSequence.right (E : StableExactSequence.{u}) :=
  E.quotient.category

/-- The quotient functor is the original native cofiber map. -/
def StableExactSequence.quotientMap (E : StableExactSequence.{u}) :
    ExactFunctor E.middle E.right := E.quotient.quotient

end MathlibExt.AlgebraicTopology.BGTVerdierQuotients
