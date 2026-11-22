/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailFreeSpan
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFreeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimitReflection

/-!
# The actual positive cone colimit on the original smaller ordinal

The original zeroth coface indexes all and only the positive vertices.
Its upper-face union is therefore the actual positive-maximum
support at every coefficient. The complete marked coefficient
colimits and their native prism charts prove the whole enriched
free colimit on the original smaller vertex and relation index.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original smaller-vertex upper-face union is exactly the whole positive-maximum coefficient support. -/
theorem coneTailUpperSupport_eq_after (n : ℕ) (i : Vertex.{u} (n + 1)) :
    coneVertexUpperSupport (coneTailEmbedding n).toOrderHom i =
      coneAfterSubcomplex i (⊥ : Vertex.{u} (n + 1)) := by
  have h : coneVertexUpperSupport (coneTailEmbedding n).toOrderHom i =
      coneAfterUpperSupport i (⊥ : Vertex.{u} (n + 1)) := by
    apply le_antisymm
    · change (⨆ j : Vertex.{u} n, coneCoordinateFace i (coneTailEmbedding n j) true) ≤
        ⨆ j : AfterVertex (⊥ : Vertex.{u} (n + 1)), coneCoordinateFace i j.val true
      apply iSup_le
      intro j
      exact le_iSup (fun j : AfterVertex (⊥ : Vertex.{u} (n + 1)) => coneCoordinateFace i j.val true)
        (coneTailVertexOrderIso n j)
    · change (⨆ j : AfterVertex (⊥ : Vertex.{u} (n + 1)), coneCoordinateFace i j.val true) ≤
        ⨆ j : Vertex.{u} n, coneCoordinateFace i (coneTailEmbedding n j) true
      apply iSup_le
      intro j
      let a := (coneTailVertexOrderIso n).symm j
      have ha : coneTailEmbedding n a = j.val :=
        congrArg Subtype.val ((coneTailVertexOrderIso n).apply_symm_apply j)
      exact (congrArg (fun x => coneCoordinateFace i x true) ha.symm).le.trans
        (le_iSup (fun j : Vertex.{u} n => coneCoordinateFace i (coneTailEmbedding n j) true) a)
  exact h.trans (coneAfterSubcomplex_eq_upper i (⊥ : Vertex.{u} (n + 1))).symm

/-- The original upper-face union point is its actual whole positive-maximum marked coefficient. -/
def coneTailUpperPointIso (n : ℕ) (i : Vertex.{u} (n + 1)) :
    (coneVertexUpperMarkedCocone (coneTailEmbedding n).toOrderHom i).pt ≅
      coneAfterWeight i (⊥ : Vertex.{u} (n + 1)) := by
  change comap (coneWeight i) (coneVertexUpperSupport (coneTailEmbedding n).toOrderHom i).ι ≅
    coneAfterWeight i (⊥ : Vertex.{u} (n + 1))
  exact isoMk (Y := coneAfterSupportMarked i (⊥ : Vertex.{u} (n + 1)))
    (Subcomplex.eqToIso (coneTailUpperSupport_eq_after n i)) (fun _ => Iff.rfl) ≪≫
      (coneAfterSupportIso i (⊥ : Vertex.{u} (n + 1))).symm

/-- The original indexed upper-face cocone keeps the genuine positive-maximum coefficient as its point. -/
def coneTailUpperCocone (n : ℕ) (i : Vertex.{u} (n + 1)) :
    Multicofork (coneVertexUpperMarkedSpan (coneTailEmbedding n).toOrderHom i) :=
  (coneVertexUpperMarkedCocone (coneTailEmbedding n).toOrderHom i).extend (coneTailUpperPointIso n i).hom

/-- The actual indexed marked upper-face cocone is genuinely colimiting on the same original positive coefficient. -/
def coneTailUpperIsColimit (n : ℕ) (i : Vertex.{u} (n + 1)) : IsColimit (coneTailUpperCocone n i) :=
  IsColimit.ofIsoColimit (coneVertexUpperMarkedIsColimit (coneTailEmbedding n).toOrderHom i)
    (Multicofork.ext (coneTailUpperPointIso n i) (fun _ => rfl))

/-- Each original indexed upper-face prism has exactly the same whole native free tail leg. -/
theorem coneTailUpperPrism_inv_leg (n : ℕ) (i : Vertex.{u} (n + 1)) (j : Vertex.{u} n) :
    (coneUpperFacePrismIso i (coneTailEmbedding n j)).inv ≫ (coneTailUpperCocone n i).π j =
      (coneTailFreeLeg n j).app (op (SimplicialThickening.mk i)) := by
  rw [coneTailFreeLeg_app]
  apply Hom.ext
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  refine CategoryTheory.Functor.ext (fun _ => Subtype.ext rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The same original upper-face chart carries the actual free leg to its whole coefficient cocone inclusion. -/
theorem coneTailUpperPrism_hom_leg (n : ℕ) (i : Vertex.{u} (n + 1)) (j : Vertex.{u} n) :
    (coneUpperFacePrismIso i (coneTailEmbedding n j)).hom ≫
      (coneTailFreeLeg n j).app (op (SimplicialThickening.mk i)) = (coneTailUpperCocone n i).π j := by
  let e := coneUpperFacePrismIso i (coneTailEmbedding n j)
  have h := coneTailUpperPrism_inv_leg n i j
  exact (congrArg (fun f => e.hom ≫ f) h.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ (coneTailUpperCocone n i).π j) e.hom_inv_id).trans (Category.id_comp _)))

/-- The original smaller-index free cocone gives the actual full marked positive-cone colimit at each
  original coefficient. -/
def coneTailFreeValueIsColimit (n : ℕ) (i : Vertex.{u} (n + 1)) :
    IsColimit ((enrichedDiagramEvaluation (Index.{u} (n + 1))ᵒᵖ
      (op (SimplicialThickening.mk i))).mapCocone (coneTailFreeCocone n)) := by
  refine (IsColimit.equivOfNatIsoOfIso (coneVertexFreeEvaluationIso (coneTailEmbedding n).toOrderHom i)
    _ (coneTailUpperCocone n i) ?_).symm (coneTailUpperIsColimit n i)
  refine Multicofork.ext (Iso.refl _) ?_
  intro j
  change ((coneUpperFacePrismIso i (coneTailEmbedding n j)).hom ≫
    (coneTailFreeLeg n j).app (op (SimplicialThickening.mk i))) ≫ 𝟙 _ = (coneTailUpperCocone n i).π j
  exact (Category.comp_id _).trans (coneTailUpperPrism_hom_leg n i j)

/-- The original smaller ordinal presents the whole actual positive cone by its original free coefficients
  and whole path relations. -/
def coneTailFreeIsColimit (n : ℕ) : IsColimit (coneTailFreeCocone.{u} n) := by
  apply enrichedIsColimitOfEvaluation
  intro i
  exact coneTailFreeValueIsColimit n i.unop.as

end SSet.Marked.CoherentWeight
