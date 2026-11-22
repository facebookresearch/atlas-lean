/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryValues
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The actual complete root-boundary enriched pushout

The genuine marked pushouts at every original evaluation coefficient
prove the whole original enriched pushout. Cobase change of the actual
marked root-boundary free inclusion gives the supported diagram's
projective left class, preserving its same inclusion in the whole cone.
No native boundary-chart identification or Quillen conclusion is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The complete original root-boundary cell attaches by its actual whole enriched square. -/
def coneRootBoundaryEnrichedCocone (n : ℕ) :
    PushoutCocone (coneRootBoundaryCellFreeMap.{u} n) (coneRootBoundaryFreeLeg n) :=
  PushoutCocone.mk (coneRootFreeMap n) (coneRootBoundaryDiagramInclusion n)
    (coneRootBoundaryCell_condition n)

/-- The same full original cone is the actual marked enriched pushout of the complete root-boundary free cell. -/
def coneRootBoundaryEnrichedIsColimit (n : ℕ) :
    IsColimit (coneRootBoundaryEnrichedCocone.{u} n) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ i)
      (coneRootBoundaryCellFreeMap n) (coneRootBoundaryFreeLeg n))
    ((enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ i).mapCocone (coneRootBoundaryEnrichedCocone n))
    (coneRootBoundaryComponentCocone n i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm
        (coneRootBoundaryComponentIsColimit n i.unop.as)
  · change (coneRootFreeMap n).app i ≫ 𝟙 _ = (coneRootFreeMap n).app i
    exact Category.comp_id _
  · change (coneRootBoundaryDiagramInclusion n).app i ≫ 𝟙 _ =
      (coneRootBoundaryDiagramInclusion n).app i
    exact Category.comp_id _

/-- The unchanged actual complete root-boundary inclusion has genuine projective left lifting in all original
dimensions and value universes. -/
theorem coneRootBoundaryInclusion_projectiveLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} n)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (coneRootBoundaryDiagramInclusion.{u} n) := by
  have hp : IsPushout (coneRootBoundaryCellFreeMap n) (coneRootBoundaryFreeLeg n)
      (coneRootFreeMap n) (coneRootBoundaryDiagramInclusion n) :=
    IsPushout.of_isColimit (coneRootBoundaryEnrichedIsColimit n)
  exact MorphismProperty.of_isPushout hp.flip (coneRootBoundaryCellFreeMap_projectiveLeft n)

end SSet.Marked.CoherentWeight
