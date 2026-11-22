/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFreeSpan
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeVertexUpperSpan

/-!
# Whole marked coefficient charts of the native free cone relations

The native free coefficient at each designated vertex is the entire
upper-face prism at every original evaluation vertex. The native
relation is the entire two-path intersection prism. Both original
relation maps become the actual intersection inclusions under these
strict marked charts, including repeated-image vertices.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable {n : ℕ} {ι : Type v} [LinearOrder ι] (e : ι →o Vertex.{u} n) (i : Vertex.{u} n)

/-- The first original free relation acts on the last coefficient and retains the entire first path. -/
theorem coneVertexFreeSpan_first_app (p : (MultispanShape.ofLinearOrder ι).L) :
    ((coneVertexFreeSpan e).fst p).app (op (SimplicialThickening.mk i)) =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i (e p.val.1)))))
        (coneAction (e p.val.1) (e p.val.2)) := rfl

/-- The second original free relation is precisely the full original coherent two-path composition map. -/
theorem coneVertexFreeSpan_second_app (p : (MultispanShape.ofLinearOrder ι).L) :
    ((coneVertexFreeSpan e).snd p).app (op (SimplicialThickening.mk i)) =
      coneFreeTwoPathAction i (e p.val.1) (e p.val.2) := by
  let A := coneVertexRelationValue e p
  let F := coneVertexFreeObject e p.val.2
  let c := op (SimplicialThickening.mk (e p.val.1))
  let x := op (SimplicialThickening.mk i)
  change prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) (𝟙 A) ≫ enrichedDiagramAction F c x = _
  exact (congrArg (fun f => f ≫ enrichedDiagramAction F c x) (prodMap_id _ _)).trans
    (Category.id_comp _)

/-- Every evaluated native free relation diagram is exactly the whole marked upper-face diagram for the same
  original vertex family. -/
def coneVertexFreeEvaluationIso :
    (coneVertexFreeSpan e).multispan ⋙
        enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk i)) ≅
      (coneVertexUpperMarkedSpan e i).multispan := by
  refine WalkingMultispan.functorExt
    (fun p => (coneUpperPairPrismIso (i := i) (e.monotone (le_of_lt p.property))).symm)
    (fun j => (coneUpperFacePrismIso i (e j)).symm) ?_ ?_
  · intro p
    change prodMap (𝟙 (max (nerve (SimplicialThickening.Path i (e p.val.1)))))
        (coneAction (e p.val.1) (e p.val.2)) ≫ (coneUpperFacePrismIso i (e p.val.1)).inv =
      (coneUpperPairPrismIso (i := i) (e.monotone (le_of_lt p.property))).inv ≫
        coneUpperPairFirst i (e p.val.1) (e p.val.2)
    exact (coneUpperPairPrism_inv_first (i := i) (e.monotone (le_of_lt p.property))).symm
  · intro p
    change ((coneVertexFreeSpan e).snd p).app (op (SimplicialThickening.mk i)) ≫
        (coneUpperFacePrismIso i (e p.val.2)).inv =
      (coneUpperPairPrismIso (i := i) (e.monotone (le_of_lt p.property))).inv ≫
        coneUpperPairSecond i (e p.val.1) (e p.val.2)
    exact (congrArg (fun f => f ≫ (coneUpperFacePrismIso i (e p.val.2)).inv)
      (coneVertexFreeSpan_second_app e i p)).trans
      (coneUpperPairPrism_inv_second (i := i) (e.monotone (le_of_lt p.property))).symm

/-- The original whole upper-face chart carries the actual native free leg to the same original face inclusion. -/
theorem coneVertexUpperFace_hom_leg (j : ι) :
    (coneUpperFacePrismIso i (e j)).hom ≫
      (coneVertexFreeLeg e j).app (op (SimplicialThickening.mk i)) = coneUpperFaceInclusion i (e j) := by
  rw [coneVertexFreeLeg_app]
  let d := coneUpperFacePrismIso i (e j)
  have h := coneUpperFacePrism_inv_inclusion i (e j)
  exact (congrArg (fun f => d.hom ≫ f) h.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ coneUpperFaceInclusion i (e j)) d.hom_inv_id).trans (Category.id_comp _)))

end SSet.Marked.CoherentWeight
