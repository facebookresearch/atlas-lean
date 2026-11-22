/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalMarkingEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# Both genuine whole original critical predecessor marking pushouts

The actual marked colimit at every original coefficient gives the full
enriched colimit of both the original cone and terminal horn marking
squares. The same original free interval marking cell, complete path
actions, all inherited supports and the original horn inclusion remain.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The entire ORIGINAL critical cone attaches the SAME original predecessor free marking cell. -/
def coneCriticalEdgeConeEnrichedCocone (n : ℕ) :
    PushoutCocone (coneCriticalEdgeFreeMap n) (coneCriticalEdgeConeMinimalLeg n) :=
  PushoutCocone.mk (coneCriticalEdgeConeSharpLeg n) (coneCriticalDiagramMark n)
    (coneCriticalEdgeConeFree_condition n)

/-- Actual whole marked evaluation proves the genuine full original critical cone marking pushout. -/
def coneCriticalEdgeConeEnrichedIsColimit (n : ℕ) :
    IsColimit (coneCriticalEdgeConeEnrichedCocone.{u} n) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} (n + 2))ᵒᵖ i)
      (coneCriticalEdgeFreeMap n) (coneCriticalEdgeConeMinimalLeg n))
    ((enrichedDiagramEvaluation (Index.{u} (n + 2))ᵒᵖ i).mapCocone (coneCriticalEdgeConeEnrichedCocone n))
    (coneCriticalEdgeConeComponentCocone n i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm (coneCriticalEdgeConeComponentIsColimit n i.unop.as)
  · exact Category.comp_id _
  · exact Category.comp_id _

/-- The SAME full original terminal horn attaches that exact original predecessor free marking cell. -/
def coneCriticalEdgeHornEnrichedCocone (n : ℕ) :
    PushoutCocone (coneCriticalEdgeFreeMap n) (coneCriticalEdgeHornMinimalLeg n) :=
  PushoutCocone.mk (coneCriticalEdgeHornSharpLeg n) (coneCriticalHornDiagramMark n)
    (coneCriticalEdgeHornFree_condition n)

/-- Every entire original marked coefficient proves the genuine full enriched critical horn marking pushout. -/
def coneCriticalEdgeHornEnrichedIsColimit (n : ℕ) :
    IsColimit (coneCriticalEdgeHornEnrichedCocone.{u} n) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} (n + 2))ᵒᵖ i)
      (coneCriticalEdgeFreeMap n) (coneCriticalEdgeHornMinimalLeg n))
    ((enrichedDiagramEvaluation (Index.{u} (n + 2))ᵒᵖ i).mapCocone (coneCriticalEdgeHornEnrichedCocone n))
    (coneCriticalEdgeHornComponentCocone n i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm (coneCriticalEdgeHornComponentIsColimit n i.unop.as)
  · exact Category.comp_id _
  · exact Category.comp_id _

/-- The exact original predecessor free marking map has the genuine projective left class from its actual
coefficient mono. -/
theorem coneCriticalEdgeFreeMap_projectiveLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} (n + 2))ᵒᵖ coefficientGeneratingMonos).rlp.llp (coneCriticalEdgeFreeMap n) :=
  enrichedFree_markedMono_left (Index.{u} (n + 2))ᵒᵖ
    (op (SimplicialThickening.mk (coneCriticalPrevious n))) coneSharpRootMarkCell

/-- The SAME entire original cone critical marking map is a genuine projective attachment through its actual
enriched pushout. -/
theorem coneCriticalDiagramMark_projectiveLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} (n + 2))ᵒᵖ coefficientGeneratingMonos).rlp.llp (coneCriticalDiagramMark n) := by
  have h := IsPushout.of_isColimit (coneCriticalEdgeConeEnrichedIsColimit.{u} n)
  exact MorphismProperty.of_isPushout h.flip (coneCriticalEdgeFreeMap_projectiveLeft n)

/-- The SAME whole original terminal horn marking map has the actual projective left class from its unchanged full
marked pushout. -/
theorem coneCriticalHornDiagramMark_projectiveLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} (n + 2))ᵒᵖ coefficientGeneratingMonos).rlp.llp (coneCriticalHornDiagramMark
      n) := by
  have h := IsPushout.of_isColimit (coneCriticalEdgeHornEnrichedIsColimit.{u} n)
  exact MorphismProperty.of_isPushout h.flip (coneCriticalEdgeFreeMap_projectiveLeft n)

end SSet.Marked.CoherentWeight
