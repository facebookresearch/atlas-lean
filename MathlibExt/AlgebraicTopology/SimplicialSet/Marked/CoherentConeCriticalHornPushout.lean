/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalMarkedEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The genuine whole original critically marked enriched horn pushout

Every actual original marked evaluation is its same full free-root
pushout. These marked evaluations prove the complete genuine enriched
colimit with the original critical coefficients, whole path actions
and both exact attaching maps. Cobase change of the actual original
critical coefficient weak free cell gives the genuine weak projective
left class of the SAME entire supported critical horn inclusion.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The complete SAME original critically marked free-root square retains its actual whole enriched critical cone as
its point. -/
def coneCriticalHornEnrichedCocone (n : ℕ) :
    PushoutCocone (coneCriticalHornCellFreeMap.{u} n) (coneCriticalHornFreeLeg n) :=
  PushoutCocone.mk (coneCriticalRootFreeLeg n) (coneCriticalHornInclusion n) (coneCriticalHornCell_condition n)

/-- The entire SAME original critically marked cone is genuinely the full marked enriched pushout of its original
complete free-root horn cell. -/
def coneCriticalHornEnrichedIsColimit (n : ℕ) : IsColimit (coneCriticalHornEnrichedCocone.{u} n) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} (n + 2))ᵒᵖ i)
      (coneCriticalHornCellFreeMap n) (coneCriticalHornFreeLeg n))
    ((enrichedDiagramEvaluation (Index.{u} (n + 2))ᵒᵖ i).mapCocone (coneCriticalHornEnrichedCocone n))
    (coneCriticalHornComponentCocone n i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm (coneCriticalHornComponentIsColimit n i.unop.as)
  · change (coneCriticalRootFreeLeg n).app i ≫ 𝟙 _ = (coneCriticalRootFreeLeg n).app i
    exact Category.comp_id _
  · change (coneCriticalHornInclusion n).app i ≫ 𝟙 _ = (coneCriticalHornInclusion n).app i
    exact Category.comp_id _

/-- The SAME entire original critically marked supported horn inclusion has its genuine full weak projective left
class through the actual original whole marked free-root pushout. -/
theorem coneCriticalHornInclusion_projectiveWeakLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} (n + 2))ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp (coneCriticalHornInclusion
      n) := by
  have h : IsPushout (coneCriticalHornCellFreeMap n) (coneCriticalHornFreeLeg n)
      (coneCriticalRootFreeLeg n) (coneCriticalHornInclusion n) := IsPushout.of_isColimit
        (coneCriticalHornEnrichedIsColimit n)
  exact MorphismProperty.of_isPushout h.flip (coneCriticalHornCellFreeMap_projectiveWeakLeft n)

end SSet.Marked.CoherentWeight
