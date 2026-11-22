/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSharpRootMarkValues
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The genuine original sharp interval free-root enriched pushout

Actual marked evaluation proves the full enriched pushout of the same
original root marking cell. Cobase change of its genuine free marked
mono proves the original whole interval maximalization map has the
projective left class, preserving every original path action and mark.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The entire original sharp interval attaches by the actual full enriched root marking square. -/
def coneSharpRootMarkEnrichedCocone : PushoutCocone coneSharpRootMarkFreeMap.{u} (coneRootFreeMap 1) :=
  PushoutCocone.mk coneSharpRootFreeLeg (coneSharp 1) coneSharpRootMark_condition

/-- The unchanged original sharp interval is genuinely the marked enriched pushout of its actual original free root
marking cell. -/
def coneSharpRootMarkEnrichedIsColimit : IsColimit coneSharpRootMarkEnrichedCocone.{u} := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} 1)ᵒᵖ i)
      coneSharpRootMarkFreeMap (coneRootFreeMap 1))
    ((enrichedDiagramEvaluation (Index.{u} 1)ᵒᵖ i).mapCocone coneSharpRootMarkEnrichedCocone)
    (coneSharpRootMarkComponentCocone i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm (coneSharpRootMarkComponentIsColimit i.unop.as)
  · exact Category.comp_id _
  · exact Category.comp_id _

/-- The same original whole sharp interval map has the genuine projective left class by its actual full marked
free-root enriched pushout. -/
theorem coneSharpInterval_projectiveLeft :
    (enrichedFreeGenerators (Index.{u} 1)ᵒᵖ coefficientGeneratingMonos).rlp.llp (coneSharp 1) := by
  have h : IsPushout coneSharpRootMarkFreeMap (coneRootFreeMap 1) coneSharpRootFreeLeg (coneSharp 1) :=
    IsPushout.of_isColimit coneSharpRootMarkEnrichedIsColimit
  exact MorphismProperty.of_isPushout h.flip coneSharpRootMarkFreeMap_projectiveLeft

end SSet.Marked.CoherentWeight
