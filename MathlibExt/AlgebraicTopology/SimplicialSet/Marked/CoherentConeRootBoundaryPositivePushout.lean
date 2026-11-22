/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryPositiveValues
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The actual original marked positive/free-root enriched pushout

Genuine marked pushouts at every original coefficient give the whole
original enriched colimit by actual marked evaluation reflection.
Its point is precisely the same supported root-boundary diagram,
retaining all original positive/free-root maps and path actions.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual original positive/free-root square has exactly the same whole marked supported root-boundary diagram
as its enriched point. -/
def coneRootBoundaryPositiveEnrichedCocone (n : ℕ) :
    PushoutCocone (conePositiveBoundaryFreeMap.{u} n) (conePositiveRootFreeLeg n) :=
  PushoutCocone.mk (coneRootBoundaryFreeLeg n) (coneRootBoundaryAfterMap n) (coneRootBoundaryPositive_condition n)

/-- The complete original marked root-boundary diagram is genuinely the full enriched pushout of its unchanged
original positive diagram and free-root boundary coefficient. -/
def coneRootBoundaryPositiveEnrichedIsColimit (n : ℕ) :
    IsColimit (coneRootBoundaryPositiveEnrichedCocone.{u} n) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ i)
      (conePositiveBoundaryFreeMap n) (conePositiveRootFreeLeg n))
    ((enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ i).mapCocone (coneRootBoundaryPositiveEnrichedCocone n))
    (coneRootBoundaryPositiveComponentCocone n i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm (coneRootBoundaryPositiveComponentIsColimit n i.unop.as)
  · change (coneRootBoundaryFreeLeg n).app i ≫ 𝟙 _ = (coneRootBoundaryFreeLeg n).app i
    exact Category.comp_id _
  · change (coneRootBoundaryAfterMap n).app i ≫ 𝟙 _ = (coneRootBoundaryAfterMap n).app i
    exact Category.comp_id _

end SSet.Marked.CoherentWeight
