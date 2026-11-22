/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeMarkedCofibrations

/-!
# The same entire supported root-horn attachment is cofibrant

Every original supported root-horn coefficient enters the whole
original cone by its genuine marked monomorphism. Its same original
free-root map and actual complete marked enriched pushout give the full
projective left class for every omitted coordinate. This includes the
original terminal coordinate with its unchanged marking.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The same original root-horn free map has the actual full projective mono left class at every omitted coordinate
through its genuine marked coefficient inclusion. -/
theorem coneRootHornCellFreeMap_projectiveLeft {n : ℕ} (k : Fin (n + 2)) :
    (enrichedFreeGenerators (Index.{u} (n + 1))ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (coneRootHornCellFreeMap k) :=
  enrichedFree_markedMono_left (Index.{u} (n + 1))ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
      (coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1)))

/-- Every same whole original supported-horn inclusion is genuinely projectively left through its actual original
complete marked free-root pushout. -/
theorem coneRootHornInclusion_projectiveLeft {n : ℕ} (k : Fin (n + 2)) :
    (enrichedFreeGenerators (Index.{u} (n + 1))ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (coneRootHornDiagramInclusion k) := by
  have h : IsPushout (coneRootHornCellFreeMap k) (coneRootHornFreeLeg k)
      (coneRootFreeMap (n + 1)) (coneRootHornDiagramInclusion k) :=
    IsPushout.of_isColimit (coneRootHornEnrichedIsColimit k)
  exact MorphismProperty.of_isPushout h.flip (coneRootHornCellFreeMap_projectiveLeft k)

end SSet.Marked.CoherentWeight
