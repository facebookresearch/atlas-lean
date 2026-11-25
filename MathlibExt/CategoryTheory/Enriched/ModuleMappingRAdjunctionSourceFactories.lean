/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAdjunctionComponents
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSourceComponents

/-!
# Original selected sources of the Mapping_R adjunction factories

These equalities identify the whole adjunction constructors in the original
selected Day world. They retain the complete relative tensor, the actual
translated equalizer functor, and the original full comparison isomorphism.
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

/-- The whole selected stock left adjunction is the original balanced source adjunction. -/
theorem stockLeftAdjunction_eq_source (M : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    letI := moduleMonoidal d b S L B
    stockLeftAdjunction d b S L B M =
      RightModuleMappingEnd.stockAdjunction (⟨S⟩ : EnrichedFunctorCat V I) M := rfl

/-- The whole selected left adjunction retains the original source-comparison transport. -/
theorem leftAdjunction_eq_source (M : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    letI := moduleMonoidal d b S L B
    leftAdjunction d b S L B M =
      RightModuleMappingEnd.leftAdjunction (⟨S⟩ : EnrichedFunctorCat V I) M := rfl

/-- The whole source-oriented adjunction retains the original full relative tensor braid. -/
theorem adjunction_eq_source (M : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    letI := moduleMonoidal d b S L B
    adjunction d b S L B M =
      RightModuleMappingEnd.adjunction (⟨S⟩ : EnrichedFunctorCat V I) M := rfl

/-- The actual right-oriented adjunction is the actual left adjunction with its full braid. -/
theorem adjunction_eq_ofNatIsoLeft (M : Module d S L) :
    letI := moduleMonoidal d b S L B
    letI := moduleSymmetric d b S L B
    adjunction d b S L B M =
      (leftAdjunction d b S L B M).ofNatIsoLeft (tensorLeftIsoTensorRight M) := rfl

end CategoryTheory.Enriched.ModuleMappingR
