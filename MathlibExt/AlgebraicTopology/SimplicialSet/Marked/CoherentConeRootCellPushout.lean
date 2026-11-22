/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCellValues
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The true whole original enriched root attachment

The actual original positive-maximum diagram and root free coefficient
attach by their complete native maps. Genuine marked evaluation
pushouts at all original coefficients prove the whole enriched pushout,
retaining every Hom action and operator. The actual root boundary free
map is projectively cofibrant; cobase change proves the original full
positive-maximum inclusion has the genuine projective left class.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The entire original enriched root attachment is its actual native square. -/
def coneRootCellEnrichedCocone (n : ℕ) :
    PushoutCocone (coneRootBoundaryFreeMap.{u} n) (coneAfterRootFreeMap n) :=
  PushoutCocone.mk (coneRootFreeMap n) (coneAfterDiagramInclusion (⊥ : Vertex.{u} n))
    (coneRootCell_condition n)

/-- The full original cone is the genuine marked enriched pushout of its original positive-maximum diagram
  and actual root free coefficient. -/
def coneRootCellEnrichedIsColimit (n : ℕ) : IsColimit (coneRootCellEnrichedCocone.{u} n) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ i)
      (coneRootBoundaryFreeMap n) (coneAfterRootFreeMap n))
    ((enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ i).mapCocone (coneRootCellEnrichedCocone n))
    (coneRootCellComponentCocone n i.unop.as) (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm
      (coneRootCellComponentIsColimit n i.unop.as)
  · change (coneRootFreeMap n).app i ≫ 𝟙 _ = (coneRootFreeMap n).app i
    exact Category.comp_id _
  · change (coneAfterDiagramInclusion (⊥ : Vertex.{u} n)).app i ≫ 𝟙 _ =
      (coneAfterDiagramInclusion (⊥ : Vertex.{u} n)).app i
    exact Category.comp_id _

/-- The actual full original positive-maximum cone inclusion is projectively cofibrant at every original
  degree and value universe, by its genuine root free-cell pushout. -/
theorem coneAfterRootInclusion_projectiveLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} n)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (coneAfterDiagramInclusion (⊥ : Vertex.{u} n)) := by
  have hp : IsPushout (coneRootBoundaryFreeMap n) (coneAfterRootFreeMap n)
      (coneRootFreeMap n) (coneAfterDiagramInclusion (⊥ : Vertex.{u} n)) :=
    IsPushout.of_isColimit (coneRootCellEnrichedIsColimit n)
  exact MorphismProperty.of_isPushout hp.flip (coneRootBoundaryFreeMap_projectiveLeft n)

end SSet.Marked.CoherentWeight
