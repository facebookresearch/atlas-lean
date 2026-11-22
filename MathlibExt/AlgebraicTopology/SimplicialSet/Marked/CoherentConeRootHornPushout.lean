/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornValues
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The SAME actual original entire root-horn enriched pushout and weak left class

The genuine original marked pushouts at every evaluation coefficient give
the entire original enriched pushout. Cobase change of the actual
original coefficient weak free-root map gives the SAME supported
inclusion's full original weak-mono projective left class. Every original
whole map, path action and marked coefficient remains retained.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The SAME original entire root-horn cell attaches through its actual full original enriched square. -/
def coneRootHornEnrichedCocone {n : ℕ} (k : Fin (n + 2)) :
    PushoutCocone (coneRootHornCellFreeMap.{u} k) (coneRootHornFreeLeg k) :=
  PushoutCocone.mk (coneRootFreeMap (n + 1)) (coneRootHornDiagramInclusion k) (coneRootHornCell_condition k)

/-- The SAME full original cone is the actual entire marked enriched pushout of its unchanged complete original
root-horn free-cell square. -/
def coneRootHornEnrichedIsColimit {n : ℕ} (k : Fin (n + 2)) :
    IsColimit (coneRootHornEnrichedCocone.{u} k) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} (n + 1))ᵒᵖ i)
      (coneRootHornCellFreeMap k) (coneRootHornFreeLeg k))
    ((enrichedDiagramEvaluation (Index.{u} (n + 1))ᵒᵖ i).mapCocone (coneRootHornEnrichedCocone k))
    (coneRootHornComponentCocone k i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm (coneRootHornComponentIsColimit k i.unop.as)
  · change (coneRootFreeMap (n + 1)).app i ≫ 𝟙 _ = (coneRootFreeMap (n + 1)).app i
    exact Category.comp_id _
  · change (coneRootHornDiagramInclusion k).app i ≫ 𝟙 _ = (coneRootHornDiagramInclusion k).app i
    exact Category.comp_id _

/-- The SAME original entire supported root-horn inclusion has the genuine full weak-mono projective left class
through its actual original free-root pushout. -/
theorem coneRootHornInclusion_projectiveWeakLeft {n : ℕ} (k : Fin (n + 2)) (hk : 0 < k)
    (hk' : k < Fin.last (n + 1)) :
    (enrichedFreeGenerators (Index.{u} (n + 1))ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (coneRootHornDiagramInclusion k) := by
  have hp : IsPushout (coneRootHornCellFreeMap k) (coneRootHornFreeLeg k)
      (coneRootFreeMap (n + 1)) (coneRootHornDiagramInclusion k) :=
    IsPushout.of_isColimit (coneRootHornEnrichedIsColimit k)
  exact MorphismProperty.of_isPushout hp.flip (coneRootHornCellFreeMap_projectiveWeakLeft k hk hk')

end SSet.Marked.CoherentWeight
