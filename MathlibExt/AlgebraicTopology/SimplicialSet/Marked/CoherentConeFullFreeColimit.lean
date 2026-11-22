/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFreeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The full original cone as its genuine native free colimit

All original vertices and their whole coherent path relations present
the full cone diagram. At every coefficient the upper face at its own
least vertex is the entire original cone. The same marked upper-face
colimit and whole native prism charts therefore prove the actual
enriched presentation in every dimension and value universe.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- All original upper faces cover the full original coefficient, since its own least vertex is retained. -/
theorem coneFullUpperSupport_eq_top {n : ℕ} (i : Vertex.{u} n) :
    coneVertexUpperSupport (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i = ⊤ := by
  apply top_unique
  calc
    ⊤ = coneCoordinateFace i i true := (coneCoordinateFace_self_true i).symm
    _ ≤ coneVertexUpperSupport (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i :=
      le_iSup (fun j => coneCoordinateFace i j true) i

/-- The actual marked full upper-face union is the whole original cone coefficient with its original marks. -/
def coneFullUpperPointIso (n : ℕ) (i : Vertex.{u} n) :
    (coneVertexUpperMarkedCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i).pt ≅ coneWeight i :=
  isoMk (Subcomplex.eqToIso (coneFullUpperSupport_eq_top i) ≪≫
    Subcomplex.topIso (nerve (ConeSubset i))) (fun _ => Iff.rfl)

/-- The full original cone coefficient has the original complete upper-face intersection cocone. -/
def coneFullUpperCocone (n : ℕ) (i : Vertex.{u} n) :
    Multicofork (coneVertexUpperMarkedSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i) :=
  Multicofork.ofπ _ (coneWeight i) (fun j => coneUpperFaceInclusion i j)
    (fun p => (coneUpperPairFirst_inclusion i p.val.1 p.val.2).trans
      (coneUpperPairSecond_inclusion i p.val.1 p.val.2).symm)

/-- The full marked coefficient is genuinely colimiting for its same original upper faces and intersections. -/
def coneFullUpperIsColimit (n : ℕ) (i : Vertex.{u} n) : IsColimit (coneFullUpperCocone n i) := by
  refine IsColimit.ofIsoColimit
    (coneVertexUpperMarkedIsColimit (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i) ?_
  refine Multicofork.ext (coneFullUpperPointIso n i) ?_
  intro j
  apply Hom.ext
  rfl

/-- The whole original free-vertex cocone is colimiting at every original coefficient. -/
def coneFullFreeValueIsColimit (n : ℕ) (i : Vertex.{u} n) :
    IsColimit ((enrichedDiagramEvaluation (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk i))).mapCocone
      (coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n))) := by
  refine (IsColimit.equivOfNatIsoOfIso
    (coneVertexFreeEvaluationIso (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i)
    _ (coneFullUpperCocone n i) ?_).symm (coneFullUpperIsColimit n i)
  refine Multicofork.ext (Iso.refl _) ?_
  intro j
  change ((coneUpperFacePrismIso i j).hom ≫
    (coneVertexFreeLeg (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) j).app
      (op (SimplicialThickening.mk i))) ≫ 𝟙 _ = coneUpperFaceInclusion i j
  exact (Category.comp_id _).trans
    (coneVertexUpperFace_hom_leg (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) i j)

/-- The full original cone diagram is the genuine enriched colimit of its original free coefficients and
  full coherent path relations. -/
def coneFullFreeIsColimit (n : ℕ) :
    IsColimit (coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  exact coneFullFreeValueIsColimit n i.unop.as

end SSet.Marked.CoherentWeight
