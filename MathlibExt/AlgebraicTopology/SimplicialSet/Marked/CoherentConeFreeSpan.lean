/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeCoefficientNaturality
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Native free cone-vertex relation diagrams

An ordered family of original vertices gives native free cone
coefficients and whole coherent path relations. The relation maps
are the original cone action and the genuine free evaluation map.
The canonical cocone uses the full original cone actions. No diagram
model structure or source-presentation outcome is part of the data.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable {n : ℕ} {ι : Type v} [LinearOrder ι] (e : ι →o Vertex.{u} n)

/-- Each designated original vertex contributes its actual free cone coefficient. -/
def coneVertexFreeObject (j : ι) : EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e j))) (coneWeight (e j))

/-- Every ordered relation retains the whole original path and last cone coefficient. -/
def coneVertexRelationValue (p : (MultispanShape.ofLinearOrder ι).L) : Marked.{u} :=
  prod (max (nerve (SimplicialThickening.Path (e p.val.1) (e p.val.2)))) (coneWeight (e p.val.2))

/-- The native free-vertex relation diagram keeps the original action and free evaluation maps. -/
def coneVertexFreeSpan : MultispanIndex (.ofLinearOrder ι) (EnrichedDiagram (Index.{u} n)ᵒᵖ) where
  left p := enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e p.val.1)))
    (coneVertexRelationValue (ι := ι) e p)
  right j := coneVertexFreeObject (ι := ι) e j
  fst p := (enrichedFreeDiagramFunctor (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e p.val.1)))).map
    (coneAction (e p.val.1) (e p.val.2))
  snd p := enrichedFreeExtend (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e p.val.1)))
    (coneVertexRelationValue (ι := ι) e p) (coneVertexFreeObject (ι := ι) e p.val.2) (𝟙 _)

/-- The original free cone coefficient enters the original whole cone by its identity coefficient extension. -/
def coneVertexFreeLeg (j : ι) : coneVertexFreeObject e j ⟶ coneDiagram n :=
  enrichedFreeExtend (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (e j))) (coneWeight (e j))
    (coneDiagram n) (𝟙 (coneWeight (e j)))

/-- Every full coefficient of the canonical free leg is precisely the original cone path action. -/
theorem coneVertexFreeLeg_app (i : Vertex.{u} n) (j : ι) :
    (coneVertexFreeLeg e j).app (op (SimplicialThickening.mk i)) = coneAction i (e j) := by
  change prodMap (𝟙 (max (nerve (SimplicialThickening.Path i (e j))))) (𝟙 (coneWeight (e j))) ≫
    maxUncurry (maxCurry (coneAction i (e j))) = _
  rw [prodMap_id, Category.id_comp, maxUncurry_maxCurry]

/-- The two complete original path relations agree through their original cone legs. -/
theorem coneVertexFreeSpan_condition (p : (MultispanShape.ofLinearOrder ι).L) :
    (coneVertexFreeSpan e).fst p ≫ coneVertexFreeLeg e p.val.1 =
      (coneVertexFreeSpan e).snd p ≫ coneVertexFreeLeg e p.val.2 := by
  let C := (Index.{u} n)ᵒᵖ
  let c := op (SimplicialThickening.mk (e p.val.1))
  let A := coneVertexRelationValue e p
  change (enrichedFreeDiagramFunctor C c).map (coneAction (e p.val.1) (e p.val.2)) ≫
      enrichedFreeExtend C c (coneWeight (e p.val.1)) (coneDiagram n) (𝟙 _) =
    enrichedFreeExtend C c A (coneVertexFreeObject e p.val.2) (𝟙 A) ≫ coneVertexFreeLeg e p.val.2
  have hf := enrichedFreeExtend_pre C c (coneAction (e p.val.1) (e p.val.2)) (coneDiagram n)
    (𝟙 (coneWeight (e p.val.1)))
  have hg : coneAction (e p.val.1) (e p.val.2) ≫ 𝟙 _ =
      (coneVertexFreeLeg e p.val.2).app c :=
    (Category.comp_id _).trans (coneVertexFreeLeg_app e (e p.val.1) p.val.2).symm
  have hh : enrichedFreeExtend C c A (coneVertexFreeObject e p.val.2) (𝟙 A) ≫ coneVertexFreeLeg e p.val.2 =
      enrichedFreeExtend C c A (coneDiagram n) ((coneVertexFreeLeg e p.val.2).app c) :=
    (enrichedFreeExtend_post C c A (F := coneVertexFreeObject e p.val.2)
      (G := coneDiagram n) (𝟙 A) (coneVertexFreeLeg e p.val.2)).trans
      (congrArg (enrichedFreeExtend C c A (coneDiagram n)) (Category.id_comp _))
  exact hf.trans ((congrArg (enrichedFreeExtend C c A (coneDiagram n)) hg).trans hh.symm)

/-- The original whole cone has the canonical free-vertex and whole-path cocone. -/
def coneVertexFreeCocone : Multicofork (coneVertexFreeSpan e) :=
  Multicofork.ofπ _ (coneDiagram n) (fun j => coneVertexFreeLeg (ι := ι) e j)
    (coneVertexFreeSpan_condition e)

end SSet.Marked.CoherentWeight
