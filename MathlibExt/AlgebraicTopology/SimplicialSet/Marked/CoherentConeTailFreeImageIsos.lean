/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailFreeSpan
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeImageUnits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductAdjunction

/-!
# Actual native free-image charts for the original zeroth coface

The existing free left-extension isomorphism carries each original
free coefficient to its actual image vertex. The proved original
coface coefficient and whole-path isomorphisms then give the native
target free vertex and relation charts. Their full coefficient
action equations retain the actual original marks and unit maps.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual native free left-extension and original coefficient image give the same target free vertex. -/
def coneTailVertexImageIso (n : ℕ) (j : Vertex.{u} n) :
    EnrichedLeftKan.object (coneTailIndex n)
        ((coneVertexFreeSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).right j) ≅
      (coneTailFreeSpan n).right j :=
  enrichedLeftKanFreeIso (coneTailIndex n) (op (SimplicialThickening.mk j)) (coneWeight j) ≪≫
    (enrichedFreeDiagramFunctor (Index.{u} (n + 1))ᵒᵖ
      (op (SimplicialThickening.mk (coneTailEmbedding n j)))).mapIso (coneTailCoefficientIso n j)

/-- The original relation coefficient keeps the entire original Hom and cone under their actual coface isomorphisms. -/
def coneTailRelationCoefficientIso (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    coneVertexRelationValue (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) p ≅
      coneVertexRelationValue (coneTailEmbedding n).toOrderHom p :=
  (prodRight (coneWeight p.val.2)).mapIso (coneTailPathMarkedIso p.val.1 p.val.2) ≪≫
    (markedProductBifunctor.mapIso (coneTailCoefficientIso n p.val.2)).app
      (max (nerve (SimplicialThickening.Path (coneTailEmbedding n p.val.1) (coneTailEmbedding n p.val.2))))

/-- The whole forward relation coefficient map is precisely the two actual original coface maps. -/
theorem coneTailRelationCoefficientIso_hom (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    (coneTailRelationCoefficientIso n p).hom =
      prodMap (coneTailPathMarkedIso p.val.1 p.val.2).hom (coneTailCoefficientIso n p.val.2).hom := by
  apply Hom.ext
  rfl

/-- The actual native free left-extension and full relation coefficient image give the same target free relation. -/
def coneTailRelationImageIso (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    EnrichedLeftKan.object (coneTailIndex n)
        ((coneVertexFreeSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).left p) ≅
      (coneTailFreeSpan n).left p :=
  enrichedLeftKanFreeIso (coneTailIndex n) (op (SimplicialThickening.mk p.val.1))
      (coneVertexRelationValue (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) p) ≪≫
    (enrichedFreeDiagramFunctor (Index.{u} (n + 1))ᵒᵖ
      (op (SimplicialThickening.mk (coneTailEmbedding n p.val.1)))).mapIso
        (coneTailRelationCoefficientIso n p)

/-- The whole inverse coface coefficient reads the same original upper-value bound insertion. -/
theorem coneTailCoefficientIso_inv_after (n : ℕ) (j : Vertex.{u} n) :
    (coneTailCoefficientIso n j).inv ≫ (coneTailAfterCoefficientIso n j).hom =
      (coneAfterAboveIso (coneTailEmbedding_positive j)).inv := by
  let e := coneTailCoefficientIso n j
  change e.inv ≫ (e.hom ≫ (coneAfterAboveIso (coneTailEmbedding_positive j)).inv) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (coneAfterAboveIso (coneTailEmbedding_positive j)).inv) e.inv_hom_id).trans
      (Category.id_comp _))

/-- The whole relation coface chart commutes with the actual original action into the same positive coefficient. -/
theorem coneTailRelationCoefficientIso_action (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    (coneTailRelationCoefficientIso n p).hom ≫
        (coneAction (coneTailEmbedding n p.val.1) (coneTailEmbedding n p.val.2) ≫
          (coneAfterAboveIso (coneTailEmbedding_positive p.val.1)).inv) =
      coneAction p.val.1 p.val.2 ≫ (coneTailAfterCoefficientIso n p.val.1).hom := by
  let i := p.val.1
  let j := p.val.2
  let root : Vertex.{u} (n + 1) := ⊥
  let fi : AfterVertex root := ⟨coneTailEmbedding n i, coneTailEmbedding_positive i⟩
  let fj : AfterVertex root := ⟨coneTailEmbedding n j, coneTailEmbedding_positive j⟩
  have h := coneAfterAbove_action root fi fj
  have hm : (coneTailRelationCoefficientIso n p).hom ≫
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path fi.val fj.val)))) (coneAfterAboveIso fj.property).inv =
      prodMap (coneTailPathMarkedIso i j).hom (coneTailAfterCoefficientIso n j).hom := by
    apply Hom.ext
    rfl
  exact (congrArg (fun f => (coneTailRelationCoefficientIso n p).hom ≫ f) h).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ coneAfterAction fi.val fj.val root) hm).trans (coneTailAfter_action i j).symm))

/-- The actual inverse whole relation chart reads the same original positive-coefficient action. -/
theorem coneTailRelationCoefficientIso_inv_action (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    (coneTailRelationCoefficientIso n p).inv ≫
        (coneAction p.val.1 p.val.2 ≫ (coneTailAfterCoefficientIso n p.val.1).hom) =
      coneAction (coneTailEmbedding n p.val.1) (coneTailEmbedding n p.val.2) ≫
        (coneAfterAboveIso (coneTailEmbedding_positive p.val.1)).inv := by
  let e := coneTailRelationCoefficientIso n p
  have h := coneTailRelationCoefficientIso_action n p
  exact (congrArg (fun f => e.inv ≫ f) h.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫
        (coneAction (coneTailEmbedding n p.val.1) (coneTailEmbedding n p.val.2) ≫
          (coneAfterAboveIso (coneTailEmbedding_positive p.val.1)).inv)) e.inv_hom_id).trans (Category.id_comp _)))

end SSet.Marked.CoherentWeight
