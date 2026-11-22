/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailFreeImageIsos
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailLeftKan
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFreeLegEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanFreeNaturality

/-!
# Original unit readbacks of the native tail free-image legs

The actual inverse free-image comparisons carry the extended
original cone cocone to the original positive-cone cocone. Free
evaluation reads the existing left-extension unit and whole original
coface operator. The coefficient and full path inverses cancel by
their proved native action equations, with no new representing map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual inverse native free vertex image carries the extended original vertex leg to the same whole
  positive-cone leg. -/
theorem coneTailVertexImageIso_inv_leg (n : ℕ) (j : Vertex.{u} n) :
    (coneTailVertexImageIso n j).inv ≫
        ((EnrichedLeftKan.leftExtension (coneTailIndex n)).map
          (coneVertexFreeLeg (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) j) ≫ coneTailLeftKanMap n) =
      coneTailFreeLeg n j := by
  let C := (Index.{u} n)ᵒᵖ
  let D := (Index.{u} (n + 1))ᵒᵖ
  let c := op (SimplicialThickening.mk j)
  let d := (coneTailIndex n).obj c
  let A := coneWeight j
  let A' := coneWeight (coneTailEmbedding n j)
  let F := coneAfterDiagram (⊥ : Vertex.{u} (n + 1))
  let L := EnrichedLeftKan.leftExtension (coneTailIndex n)
  let φ := coneVertexFreeLeg (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) j
  let g := coneTailLeftKanMap n
  let t := (enrichedLeftKanFreeIso (coneTailIndex n) c A).inv ≫ (L.map φ ≫ g)
  have hu := (EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n) F).apply_symm_apply
    (coneTailOperator n)
  have ha : enrichedFreeHomEquiv D d A F t = (coneTailAfterCoefficientIso n j).hom := by
    have h0 := enrichedLeftKanFreeIso_inv_map_post (coneTailIndex n) c A φ g
    have h1 := congrArg (fun f => enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict (coneTailIndex n)).obj F)
      (φ ≫ f)) hu
    have h2 := enrichedFreeHomEquiv_post C c A φ (coneTailOperator n)
    have h3 := congrArg (fun f => f ≫ (coneTailOperator n).app c)
      (coneVertexFreeLeg_unit (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) j)
    exact h0.trans (h1.trans (h2.trans (h3.trans (Category.id_comp _))))
  have he : (coneTailVertexImageIso n j).inv ≫ (L.map φ ≫ g) =
      (enrichedFreeDiagramFunctor D d).map (coneTailCoefficientIso n j).inv ≫ t := by
    exact Category.assoc _ _ _
  have hp := enrichedFreeHomEquiv_pre D d (coneTailCoefficientIso n j).inv F t
  have hv := (congrArg (fun f => (coneTailCoefficientIso n j).inv ≫ f) ha).trans
    (coneTailCoefficientIso_inv_after n j)
  have hg : enrichedFreeHomEquiv D d A' F (coneTailFreeLeg n j) =
      (coneAfterAboveIso (coneTailEmbedding_positive j)).inv :=
    enrichedFreeExtend_unit D d A' F (coneAfterAboveIso (coneTailEmbedding_positive j)).inv
  apply (enrichedFreeHomEquiv D d A' F).injective
  exact (congrArg (enrichedFreeHomEquiv D d A' F) he).trans (hp.trans (hv.trans hg.symm))

/-- The actual inverse native free relation image carries the extended original whole relation leg to the
  same positive-cone relation leg. -/
theorem coneTailRelationImageIso_inv_leg (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    (coneTailRelationImageIso n p).inv ≫
        ((EnrichedLeftKan.leftExtension (coneTailIndex n)).map
          ((coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).ι.app (.left p)) ≫
            coneTailLeftKanMap n) =
      (coneTailFreeSpan n).fst p ≫ coneTailFreeLeg n p.val.1 := by
  let C := (Index.{u} n)ᵒᵖ
  let D := (Index.{u} (n + 1))ᵒᵖ
  let c := op (SimplicialThickening.mk p.val.1)
  let d := (coneTailIndex n).obj c
  let A := coneVertexRelationValue (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) p
  let A' := coneVertexRelationValue (coneTailEmbedding n).toOrderHom p
  let F := coneAfterDiagram (⊥ : Vertex.{u} (n + 1))
  let L := EnrichedLeftKan.leftExtension (coneTailIndex n)
  let φ := (coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).ι.app (.left p)
  let g := coneTailLeftKanMap n
  let t := (enrichedLeftKanFreeIso (coneTailIndex n) c A).inv ≫ (L.map φ ≫ g)
  have hu := (EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n) F).apply_symm_apply
    (coneTailOperator n)
  have ha : enrichedFreeHomEquiv D d A F t =
      coneAction p.val.1 p.val.2 ≫ (coneTailAfterCoefficientIso n p.val.1).hom := by
    have h0 := enrichedLeftKanFreeIso_inv_map_post (coneTailIndex n) c A φ g
    have h1 := congrArg (fun f => enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict (coneTailIndex n)).obj F)
      (φ ≫ f)) hu
    have h2 := enrichedFreeHomEquiv_post C c A φ (coneTailOperator n)
    have h3 := congrArg (fun f => f ≫ (coneTailOperator n).app c)
      (coneVertexRelationLeg_unit (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) p)
    exact h0.trans (h1.trans (h2.trans h3))
  have he : (coneTailRelationImageIso n p).inv ≫ (L.map φ ≫ g) =
      (enrichedFreeDiagramFunctor D d).map (coneTailRelationCoefficientIso n p).inv ≫ t := by
    exact Category.assoc _ _ _
  have hp := enrichedFreeHomEquiv_pre D d (coneTailRelationCoefficientIso n p).inv F t
  have hv := (congrArg (fun f => (coneTailRelationCoefficientIso n p).inv ≫ f) ha).trans
    (coneTailRelationCoefficientIso_inv_action n p)
  have hg : enrichedFreeHomEquiv D d A' F ((coneTailFreeSpan n).fst p ≫ coneTailFreeLeg n p.val.1) =
      coneAction (coneTailEmbedding n p.val.1) (coneTailEmbedding n p.val.2) ≫
        (coneAfterAboveIso (coneTailEmbedding_positive p.val.1)).inv := by
    exact (enrichedFreeHomEquiv_pre D d
      (coneAction (coneTailEmbedding n p.val.1) (coneTailEmbedding n p.val.2)) F
      (coneTailFreeLeg n p.val.1)).trans
      (congrArg (fun f => coneAction (coneTailEmbedding n p.val.1) (coneTailEmbedding n p.val.2) ≫ f)
        (enrichedFreeExtend_unit D d (coneWeight (coneTailEmbedding n p.val.1)) F
          (coneAfterAboveIso (coneTailEmbedding_positive p.val.1)).inv))
  apply (enrichedFreeHomEquiv D d A' F).injective
  exact (congrArg (enrichedFreeHomEquiv D d A' F) he).trans (hp.trans (hv.trans hg.symm))

end SSet.Marked.CoherentWeight
