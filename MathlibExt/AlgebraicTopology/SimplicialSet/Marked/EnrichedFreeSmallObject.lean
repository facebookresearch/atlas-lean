/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedEvaluationColimits
import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily
import MathlibExt.CategoryTheory.SmallObject.PresentableSources

/-!
# Actual small-object eligibility for native marked enriched free families

The index is small in the original coefficient universe, and the
original coefficient family is genuinely small. Every free source is
presentable by the actual free/evaluation adjunction and pointwise
colimit preservation. The native small-object construction therefore
applies to the entire original free family; no factorization or model
outcome is assumed. This is the source proof used for the specifically
chosen coherent-base diagram model.
-/

noncomputable section
universe u v
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C] [Small.{u} C]
    (P : MorphismProperty Marked.{u}) [P.IsSmall.{u}]

/-- The entire native free family retains its original source-object and coefficient-arrow labels. -/
abbrev enrichedFreeGenerators : MorphismProperty (EnrichedDiagram C) :=
  adjointFamilyGenerators (fun c : C => enrichedFreeDiagramFunctor C c) P

/-- Genuine presentability of every original free source proves the original-universe small-object argument. -/
theorem enrichedFreeGenerators_hasSmallObjectArgument :
    (enrichedFreeGenerators C P).HasSmallObjectArgument.{u} := by
  let _ : Small.{u} (C × P.toSet) := inferInstance
  let _ : ∀ q : C × P.toSet,
      IsPresentable.{u} ((enrichedFreeDiagramFunctor C q.1).obj q.2.1.left) :=
    fun q => enrichedFree_isPresentable C q.1 q.2.1.left
  let _ : HasColimitsOfSize.{u, u} (EnrichedDiagram C) := EnrichedColimit.hasColimits C
  let _ : LocallySmall.{u} (EnrichedDiagram C) := by
    refine ⟨fun F G => ?_⟩
    change Small.{u} (EnrichedDiagramMap F G)
    exact small_of_injective (f := EnrichedDiagramMap.app) (fun α β h => EnrichedDiagramMap.ext h)
  exact ofHoms_hasSmallObjectArgument_of_presentable
    (fun q : C × P.toSet => (enrichedFreeDiagramFunctor C q.1).map q.2.1.hom)

/-- The proved eligibility yields actual original-universe functorial free-family factors. -/
def enrichedFreeFunctorialFactorization :
    FunctorialFactorizationData (enrichedFreeGenerators C P).rlp.llp (enrichedFreeGenerators C P).rlp := by
  let _ : (enrichedFreeGenerators C P).HasSmallObjectArgument.{u} :=
    enrichedFreeGenerators_hasSmallObjectArgument C P
  exact functorialFactorizationData _ _

omit [Small.{u} C] [P.IsSmall.{u}] in
/-- The full native right class is precisely coefficient right lifting at every original enriched source object. -/
theorem enrichedFreeGenerators_rlp_iff {F G : EnrichedDiagram C} (p : F ⟶ G) :
    (enrichedFreeGenerators C P).rlp p ↔ ∀ c : C, P.rlp (p.app c) :=
  adjointFamilyGenerators_rlp_iff (fun c : C => enrichedFreeDiagramFunctor C c)
    (fun c : C => enrichedDiagramEvaluation C c) (fun c => enrichedFreeEvaluationAdjunction C c) P p

end SSet.Marked
