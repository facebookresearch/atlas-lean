/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAdjunctionBase

/-!
# Exact source factories of the translated Mapping_R functor

Each equality identifies a whole constructed functor or isomorphism in its
original selected Day category. No action, equalizer map, or adjunction data
is replaced. These boundaries let component laws use the same selected world
throughout their proof.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local irreducible] Closed.monoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

/-- The whole selected Mapping_R functor is its original right-module source construction. -/
theorem functor_eq_source (M : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    functor d b S L B M =
      RightModuleMappingEnd.functor (⟨S⟩ : EnrichedFunctorCat V I) M := rfl

/-- The whole selected stock functor is the unchanged original converted internal Hom. -/
theorem stockFunctor_eq_source (M : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    stockFunctor d b S L B M =
      RightModuleMappingEnd.stockFunctor (⟨S⟩ : EnrichedFunctorCat V I) M := rfl

/-- The natural source comparison is exactly the original whole right-module natural iso. -/
theorem comparisonNatIso_eq_source (M : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    comparisonNatIso d b S L B M =
      RightModuleMappingEnd.comparisonNatIso (⟨S⟩ : EnrichedFunctorCat V I) M := rfl

/-- The module source comparison is exactly its original whole limiting-fork iso. -/
theorem moduleComparison_eq_source (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    moduleComparison d b S L B M N =
      RightModuleMappingEnd.moduleComparison (⟨S⟩ : EnrichedFunctorCat V I) M N := rfl

/-- The selected source module is its entire original source equalizer construction. -/
theorem moduleObject_eq_source (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    moduleObject d b S L B M N =
      RightModuleMappingEnd.moduleObject (⟨S⟩ : EnrichedFunctorCat V I) M N := rfl

/-- The selected stock module is its entire unchanged converted internal-Hom construction. -/
theorem stockModule_eq_source (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    stockModule d b S L B M N =
      RightModuleMappingEnd.stockRightHom (⟨S⟩ : EnrichedFunctorCat V I) M N := rfl

end CategoryTheory.Enriched.ModuleMappingR
