/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFreeSourceAction

/-!
# Clients of generic free-source mapping actions

These clients import only the enriched source API. They check full coend shifts,
original block maps, translated comparison components, and the parameter formula
for the genuine source delta without unfolding its constructor.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Enriched.SphereOperator
open CategoryTheory.EnrichedDayKernel CategoryTheory.Enriched.ModuleMappingR
open scoped MonoidalClosed

namespace MathlibExtTest.ModuleMappingRFreeSourceActionClients

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local irreducible] FreeSourceAction.Mapping.CanonicalDelta.sourceDelta

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

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The neutral API keeps the full coefficient map before choosing any native sphere. -/
theorem shifted_coefficient (r n k a : I) (f : a ⊗ n ⟶ k) :
    coefficientHom d S n k a f ≫ GenericRightTensor.hom d S r n k =
      coefficientHom d S (n ⊗ r) (k ⊗ r) a (GenericRightTensor.label r n k a f) :=
  SphereOperator.RightShift.coefficientHom_shift d S r n k a f

/-- The source block map is the actual reassociation and braid at every index. -/
theorem original_block_label (r n a : I) :
    GenericRightTensor.label r n (n ⊗ a) a (β_ a n).hom =
      (β_ a (n ⊗ r)).hom ≫ (SphereOperator.RightShift.blockSwap r n a).hom :=
  SphereOperator.RightShift.blockSwap_label r n a

omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Generic mapping-end translation retains the full index-braiding component. -/
theorem translated_target_forward (Y : EnrichedFunctorCat V I) (r c : I) :
    component (FreeEvaluation.translationTargetIso d b Y r).hom c =
      Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom :=
  FreeSourceAction.Mapping.translationTargetIso_hom_component d b Y r c

/-- The constructed source delta evaluates to the entire original sphere action. -/
theorem source_delta_parameter (r : I) (N : Module d S L) (c : I) :
    FreeEvaluation.parameterEquiv d b S L r (S.obj r) N c
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)
      (component (SphereModuleMappingEnd.moduleMap d S L
        (FreeSourceAction.Mapping.CanonicalDelta.sourceDelta d b S L B r N)) c) =
      FreeSourceAction.Mapping.sourceDeltaAction d S L r N c :=
  FreeSourceAction.Mapping.CanonicalDelta.sourceDelta_parameter d b S L B r N c

end MathlibExtTest.ModuleMappingRFreeSourceActionClients
