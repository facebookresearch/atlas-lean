/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.MappingBifunctorFields

/-!
# Free-source module internal Hom families

For the supplied enriched monoidal index, lax braided coefficient and required colimits,
products and equalizers, restricts the module internal Hom bifunctor to the free functor
at an index. Its coefficient maps are the contravariant precomposition maps induced by
free-module morphisms.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.FreeMappingGetters

attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
  SphereModuleMappingEnd.moduleCategory MonoidalLeftAction.monoidalOppositeLeftAction

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

open EnrichedDayKernel ModuleMappingR

variable (B : EnrichedFunctor.LaxBraidedData L)

/-- The contravariant module-Hom family obtained by restricting the module bifunctor to the
primitive free functor at `r`. -/
def functor (r : I) : Vᵒᵖ ⥤ (Module d S L ⥤ Module d S L) :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free
      (⟨S⟩ : EnrichedFunctorCat V I) r).op ⋙ ModuleMappingR.moduleBifunctor d b S L B

theorem obj (r : I) (K : V) :
    (functor d b S L B r).obj (Opposite.op K) =
      ModuleMappingR.functor d b S L B (FreeEvaluation.freeAt d S L r K) := by
  rfl

theorem map_heq (r : I) {K K' : V} (i : K ⟶ K') :
    HEq ((functor d b S L B r).map i.op)
      (ModuleMappingR.moduleSourceNatTrans d b S L B
        (freeMap d S L ((Free.functor r).map i))) := by
  rfl





end OrthogonalIGeneratorProbe.FreeMappingGetters
