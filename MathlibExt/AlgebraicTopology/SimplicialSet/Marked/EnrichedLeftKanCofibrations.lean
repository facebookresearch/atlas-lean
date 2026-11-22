/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeSmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientGenerators

/-!
# Actual free-projective lifting under native enriched left extension

Whole original restriction keeps every coefficient component right
lift. The genuine marked left-extension adjunction transports the
complete free-projective left class. Its original initial comparison
therefore preserves actual projective cofibrancy without a model or
Quillen outcome supplied as an input.
-/

noncomputable section
universe u v
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]

/-- Original whole enriched restriction preserves the full original free-family right class on every same
  coefficient component. -/
theorem enrichedRestriction_freeRight (j : EnrichedFunctor SSet.{u} C D)
    (Q : MorphismProperty Marked.{u}) {F G : EnrichedDiagram D} (p : F ⟶ G)
    (hp : (enrichedFreeGenerators D Q).rlp p) :
    (enrichedFreeGenerators C Q).rlp ((enrichedDiagramRestrict j).map p) := by
  apply (enrichedFreeGenerators_rlp_iff C Q _).mpr
  intro c
  exact (enrichedFreeGenerators_rlp_iff D Q p).mp hp (j.obj c)

/-- The actual marked enriched left extension preserves the genuine full free-family projective left class
  through its proved whole adjunction. -/
theorem enrichedLeftKan_freeLeft (j : EnrichedFunctor SSet.{u} C D)
    (Q : MorphismProperty Marked.{u}) {F G : EnrichedDiagram C} (f : F ⟶ G)
    (hf : (enrichedFreeGenerators C Q).rlp.llp f) :
    (enrichedFreeGenerators D Q).rlp.llp ((EnrichedLeftKan.leftExtension j).map f) := by
  intro X Y p hp
  exact (Adjunction.hasLiftingProperty_iff (EnrichedLeftKan.adjunction j) f p).mpr
    (hf ((enrichedDiagramRestrict j).map p) (enrichedRestriction_freeRight j Q p hp))

/-- An actually projectively cofibrant original diagram has a genuinely projectively cofibrant native left
  extension relative to any actual target initial object. -/
theorem enrichedLeftKan_initialArrow_projectiveLeft (j : EnrichedFunctor SSet.{u} C D)
    (F : EnrichedDiagram C) {O : EnrichedDiagram C} (hO : IsInitial O)
    (hF : (enrichedFreeGenerators C coefficientGeneratingMonos).rlp.llp (hO.to F))
    {P : EnrichedDiagram D} (hP : IsInitial P) :
    (enrichedFreeGenerators D coefficientGeneratingMonos).rlp.llp
      (hP.to ((EnrichedLeftKan.leftExtension j).obj F)) := by
  let L := EnrichedLeftKan.leftExtension j
  let _ : PreservesColimitsOfSize.{0, 0} L := (EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits
  let _ : PreservesColimit (Functor.empty (EnrichedDiagram C)) L :=
    (inferInstance : PreservesColimitsOfShape (Discrete PEmpty.{1}) L).preservesColimit
  let hLO : IsInitial (L.obj O) := hO.isInitialObj L O
  let e : Arrow.mk (hP.to (L.obj F)) ≅ Arrow.mk (L.map (hO.to F)) :=
    Arrow.isoMk (hP.uniqueUpToIso hLO) (Iso.refl _) (hP.hom_ext _ _)
  exact ((enrichedFreeGenerators D coefficientGeneratingMonos).rlp.llp.arrow_mk_iso_iff e).mpr
    (enrichedLeftKan_freeLeft j coefficientGeneratingMonos (hO.to F) hF)

end SSet.Marked
