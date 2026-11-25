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
# Components of the actual Mapping_R adjunction constructors

The natural comparison is the original whole source/stock module comparison
at every target. These component identities keep the selected Day structure
and the literal translated equalizer functor. The unit and counit identities
at the natural-comparison boundary support the complete source formulas.
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

/-- The full selected left unit is the original stock unit followed by inverse comparison. -/
theorem leftAdjunction_unit_comparisonNatIso (M N : Module d S L) :
    letI := moduleMonoidal d b S L B
    (leftAdjunction d b S L B M).unit.app N =
      (stockLeftAdjunction d b S L B M).unit.app N ≫
        (comparisonNatIso d b S L B M).inv.app ((tensorLeft M).obj N) := rfl

/-- The full selected left counit is the forward comparison followed by stock evaluation. -/
theorem leftAdjunction_counit_comparisonNatIso (M N : Module d S L) :
    letI := moduleMonoidal d b S L B
    (leftAdjunction d b S L B M).counit.app N =
      (tensorLeft M).map ((comparisonNatIso d b S L B M).hom.app N) ≫
        (stockLeftAdjunction d b S L B M).counit.app N := rfl

end CategoryTheory.Enriched.ModuleMappingR
