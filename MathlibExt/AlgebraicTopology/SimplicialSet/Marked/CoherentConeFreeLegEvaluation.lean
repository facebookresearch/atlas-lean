/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFreeSpan

/-!
# Original unit evaluations of native cone relation legs

The free vertex leg reads the identity on the original cone
coefficient. The whole ordered relation leg reads the original
cone path action. Both follow from the existing free/evaluation
unit laws on the full original marked coefficient.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable {n : ℕ} {ι : Type v} [LinearOrder ι] (e : ι →o Vertex.{u} n)

/-- The whole original free vertex leg evaluates to the original coefficient identity. -/
theorem coneVertexFreeLeg_unit (j : ι) :
    enrichedFreeHomEquiv (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e j)))
      (coneWeight (e j)) (coneDiagram n) (coneVertexFreeLeg e j) = 𝟙 (coneWeight (e j)) :=
  enrichedFreeExtend_unit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e j)))
    (coneWeight (e j)) (coneDiagram n) (𝟙 (coneWeight (e j)))

/-- The whole original relation cocone leg evaluates to the same original cone action on its complete path
  coefficient. -/
theorem coneVertexRelationLeg_unit (p : (MultispanShape.ofLinearOrder ι).L) :
    enrichedFreeHomEquiv (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e p.val.1)))
      (coneVertexRelationValue e p) (coneDiagram n) ((coneVertexFreeCocone e).ι.app (.left p)) =
        coneAction (e p.val.1) (e p.val.2) := by
  let C := (Index.{u} n)ᵒᵖ
  let c := op (SimplicialThickening.mk (e p.val.1))
  let A := coneVertexRelationValue e p
  let a := coneAction (e p.val.1) (e p.val.2)
  change enrichedFreeHomEquiv C c A (coneDiagram n)
    ((enrichedFreeDiagramFunctor C c).map a ≫
      enrichedFreeExtend C c (coneWeight (e p.val.1)) (coneDiagram n) (𝟙 _)) = a
  have h := enrichedFreeExtend_pre C c a (coneDiagram n) (𝟙 (coneWeight (e p.val.1)))
  exact (congrArg (enrichedFreeHomEquiv C c A (coneDiagram n)) h).trans
    ((enrichedFreeExtend_unit C c A (coneDiagram n) (a ≫ 𝟙 _)).trans (Category.comp_id _))

end SSet.Marked.CoherentWeight
