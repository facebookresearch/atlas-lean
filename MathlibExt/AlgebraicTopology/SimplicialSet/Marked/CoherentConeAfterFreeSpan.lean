/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterUpperCover
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterInclusion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFreeSpan
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Original free-vertex and whole path relations for the positive cone

Each original vertex beyond the cutoff contributes its native free
marked cone coefficient. A pair of ordered vertices contributes the
entire original coherent path parameter and upper cone coefficient.
The two maps are the original cone action and the actual free
evaluation extension. Their cocone enters the original positive cone
by its genuine upper-value inclusions.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The whole positive-maximum action is the same original path-prepending map. -/
theorem coneAfterDiagram_action {n : ℕ} (k : Vertex.{u} n) (i j : Vertex.{u} n) :
    enrichedDiagramAction (coneAfterDiagram k) (op (SimplicialThickening.mk j))
      (op (SimplicialThickening.mk i)) = coneAfterAction i j k := maxUncurry_maxCurry _

/-- The original whole upper-value bound insertion commutes with the full path action. -/
theorem coneAfterAbove_action {n : ℕ} (k : Vertex.{u} n) (j l : AfterVertex k) :
    coneAction j.val l.val ≫ (coneAfterAboveIso j.property).inv =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path j.val l.val))))
        (coneAfterAboveIso l.property).inv ≫ coneAfterAction j.val l.val k := by
  apply Hom.ext
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  refine CategoryTheory.Functor.ext (fun _ => Subtype.ext rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- Each original positive vertex contributes its actual native free cone coefficient. -/
def coneAfterFreeVertex {n : ℕ} (k : Vertex.{u} n) (j : AfterVertex k) :
    EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk j.val)) (coneWeight j.val)

/-- A whole original ordered path and upper cone coefficient form the actual relation coefficient. -/
def coneAfterFreeRelationValue {n : ℕ} (k : Vertex.{u} n)
    (p : (MultispanShape.ofLinearOrder (AfterVertex k)).L) : Marked.{u} :=
  prod (max (nerve (SimplicialThickening.Path p.val.1.val p.val.2.val))) (coneWeight p.val.2.val)

/-- The positive-vertex relations retain the full original coherent Hom parameters and actual free maps. -/
def coneAfterFreeSpan {n : ℕ} (k : Vertex.{u} n) :
    MultispanIndex (.ofLinearOrder (AfterVertex k)) (EnrichedDiagram (Index.{u} n)ᵒᵖ) :=
  coneVertexFreeSpan (show AfterVertex k →o Vertex.{u} n from ⟨Subtype.val, fun _ _ h => h⟩)

/-- The original free vertex enters the positive-maximum cone by its unchanged upper-value map. -/
def coneAfterFreeLeg {n : ℕ} (k : Vertex.{u} n) (j : AfterVertex k) :
    coneAfterFreeVertex k j ⟶ coneAfterDiagram k :=
  enrichedFreeExtend (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk j.val)) (coneWeight j.val)
    (coneAfterDiagram k) (coneAfterAboveIso j.property).inv

/-- Every original free leg evaluates to its actual path action with the unchanged original upper coefficient. -/
theorem coneAfterFreeLeg_app {n : ℕ} (i k : Vertex.{u} n) (j : AfterVertex k) :
    (coneAfterFreeLeg k j).app (op (SimplicialThickening.mk i)) =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j.val))))
        (coneAfterAboveIso j.property).inv ≫ coneAfterAction i j.val k := by
  change prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j.val))))
      (coneAfterAboveIso j.property).inv ≫ maxUncurry (maxCurry (coneAfterAction i j.val k)) = _
  rw [maxUncurry_maxCurry]

/-- The complete original ordered path relation has the same actual positive-cone leg through either vertex. -/
theorem coneAfterFreeSpan_condition {n : ℕ} (k : Vertex.{u} n)
    (p : (MultispanShape.ofLinearOrder (AfterVertex k)).L) :
    (coneAfterFreeSpan k).fst p ≫ coneAfterFreeLeg k p.val.1 =
      (coneAfterFreeSpan k).snd p ≫ coneAfterFreeLeg k p.val.2 := by
  let j : AfterVertex k := p.val.1
  let l : AfterVertex k := p.val.2
  let C := (Index.{u} n)ᵒᵖ
  let c := op (SimplicialThickening.mk j.val)
  let A := prod (max (nerve (SimplicialThickening.Path j.val l.val))) (coneWeight l.val)
  change (enrichedFreeDiagramFunctor C c).map (coneAction j.val l.val) ≫
      enrichedFreeExtend C c (coneWeight j.val) (coneAfterDiagram k) (coneAfterAboveIso j.property).inv =
    enrichedFreeExtend C c A (coneAfterFreeVertex k l) (𝟙 A) ≫ coneAfterFreeLeg k l
  have hf := enrichedFreeExtend_pre C c (coneAction j.val l.val) (coneAfterDiagram k)
    (coneAfterAboveIso j.property).inv
  have hg := congrArg (enrichedFreeExtend C c A (coneAfterDiagram k))
    ((coneAfterAbove_action k j l).trans (coneAfterFreeLeg_app j.val k l).symm)
  have hh : enrichedFreeExtend C c A (coneAfterFreeVertex k l) (𝟙 A) ≫ coneAfterFreeLeg k l =
      enrichedFreeExtend C c A (coneAfterDiagram k) ((coneAfterFreeLeg k l).app c) := by
    exact (enrichedFreeExtend_post C c A (F := coneAfterFreeVertex k l)
      (G := coneAfterDiagram k) (𝟙 A) (coneAfterFreeLeg k l)).trans
      (congrArg (enrichedFreeExtend C c A (coneAfterDiagram k))
        (Category.id_comp ((coneAfterFreeLeg k l).app c)))
  exact hf.trans (hg.trans hh.symm)

/-- The actual whole positive cone has the original free-vertex/path-relation cocone. -/
def coneAfterFreeCocone {n : ℕ} (k : Vertex.{u} n) : Multicofork (coneAfterFreeSpan k) :=
  Multicofork.ofπ _ (coneAfterDiagram k) (coneAfterFreeLeg k) (coneAfterFreeSpan_condition k)

end SSet.Marked.CoherentWeight
