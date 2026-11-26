/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.SimplicialSet.SegalOuterHornCovers

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open SSet SSet.Rezk

namespace SegalOuterHornCoversTest

private def actualOriginalColimit (m : ℕ) : IsColimit (outerHornCFaceCocone.{u} m) :=
  outerHornCFaceColimit m

private theorem originalFamilyUnique (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (outerHornCFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m).map g ≫ f T = f S) :
    ∃! l : (outerHornC (m + 2) : SSet.{u}) ⟶ X,
      ∀ S, Subcomplex.homOfLE (outerHornCFace_le_C S) ≫ l = f S := by
  refine ⟨outerHornCFaceDesc m f hf, fun S => outerHornCFaceDesc_fac m f hf S, ?_⟩
  intro l hl
  exact outerHornCFaceDesc_unique m f hf l hl

private theorem originalIntersections {m : ℕ} (S T : outerHornCFaceIndex m) :
    stdSimplex.face.{u} S.val ⊓ stdSimplex.face T.val =
      stdSimplex.face (outerHornCFaceInf S T).val := outerHornCFace_intersection S T

private theorem bothOriginalFaceSquares {m : ℕ} (S T : outerHornCFaceIndex m)
    (h : S.val ⊆ T.val) :
    (outerHornCFaceIso.{u} S).hom ≫
        Subcomplex.homOfLE ((stdSimplex.face_le_face_iff _ _).mpr h) =
      stdSimplex.map (outerHornCFaceComparison S T h) ≫ (outerHornCFaceIso T).hom ∧
    Subcomplex.homOfLE ((stdSimplex.face_le_face_iff _ _).mpr h) ≫ (outerHornCFaceIso T).inv =
      (outerHornCFaceIso S).inv ≫ stdSimplex.map (outerHornCFaceComparison S T h) :=
  ⟨outerHornCFaceIso_comparison_hom S T h, outerHornCFaceIso_comparison_inv S T h⟩

private theorem arbitraryInverseWord {m d : ℕ} (S : outerHornCFaceIndex m)
    (a : (stdSimplex.face S.val : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (((outerHornCFaceIso S).inv.app (op ⦋d⦌) a) i).val = S.val.sort.idxOf (a.val i) :=
  outerHornCFaceIso_inv_coord S a i

private theorem exactIntervalPreimage {m : ℕ} (S : outerHornCFaceIndex m) :
    (outerHornCU.{u} m).preimage (outerHornCFaceMap S) =
      outerHornCIntervalCover (outerHornCFaceDim S) ∧
    (outerHornCU m ⊓ stdSimplex.face S.val).preimage (outerHornCFaceMap S) =
      outerHornCIntervalCover (outerHornCFaceDim S) :=
  ⟨outerHornCU_preimage_face S, outerHornCU_intersection_preimage S⟩

private theorem originalIntervalFamilyUnique (ell : ℕ) (hell : 1 ≤ ell) {X : SSet.{u}}
    (f : (stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) : SSet.{u}) ⟶ X)
    (g : (stdSimplex.face (Finset.Icc (0 : Fin (ell + 1)) 1) : SSet.{u}) ⟶ X)
    (h : Subcomplex.homOfLE (outerHornCInterval_vertex_le_tail ell hell) ≫ f =
      Subcomplex.homOfLE (outerHornCInterval_vertex_le_edge ell hell) ≫ g) :
    ∃! l : (outerHornCIntervalCover ell : SSet.{u}) ⟶ X,
      Subcomplex.homOfLE (le_sup_left : stdSimplex.face.{u}
        (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) ≤ outerHornCIntervalCover ell) ≫ l = f ∧
      Subcomplex.homOfLE (le_sup_right : stdSimplex.face.{u}
        (Finset.Icc (0 : Fin (ell + 1)) 1) ≤ outerHornCIntervalCover ell) ≫ l = g := by
  refine ⟨outerHornCIntervalDesc ell hell f g h,
    ⟨outerHornCIntervalDesc_tail ell hell f g h, outerHornCIntervalDesc_edge ell hell f g h⟩, ?_⟩
  intro l hl
  exact outerHornCIntervalDesc_unique ell hell f g h l hl.1 hl.2

private theorem originalDegreeTwo (S : outerHornCFaceIndex 0) :
    S.val = {0, 1} ∧ outerHornCFaceDim S = 1 ∧
      outerHornC.{u} 2 = stdSimplex.face {0, 1} ∧
        outerHornCU.{u} 0 = stdSimplex.face {0, 1} ∧ outerHornCIntervalCover.{u} 1 = ⊤ :=
  ⟨outerHornCFaceIndex_zero S, outerHornCFaceDim_zero S,
    outerHornC_two, outerHornCU_zero, outerHornCIntervalCover_one⟩

private def leftTriangle : outerHornCFaceIndex 1 := ⟨{0, 1, 2}, by decide⟩
private def rightTriangle : outerHornCFaceIndex 1 := ⟨{0, 1, 3}, by decide⟩

private theorem noOriginalCommonUpper (V : outerHornCFaceIndex 1)
    (h : leftTriangle.val ⊆ V.val) (h' : rightTriangle.val ⊆ V.val) : False := by
  apply V.property.2.2
  apply Finset.eq_univ_of_forall
  intro i
  fin_cases i
  · exact h (by decide)
  · exact h (by decide)
  · exact h (by decide)
  · exact h' (by decide)

private def sparseOriginalFace : outerHornCFaceIndex 3 := ⟨{0, 1, 3, 5}, by decide⟩

private theorem sparseOriginalIntersection :
    outerHornCU.{u} 3 ⊓ stdSimplex.face sparseOriginalFace.val =
      stdSimplex.face (sparseOriginalFace.val.erase 0) ⊔ stdSimplex.face {0, 1} :=
  outerHornCU_inf_face sparseOriginalFace

private theorem allEmbeddedOriginalFaces (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (S : outerHornCFaceIndex m) (d e : SimplexCategoryᵒᵖ)
    (q : (((outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S).obj d).obj e) :
    ((innerOuterHornCFaceDesc m f hf).app d).app e
      (((simplicialSpaceDiscrete.map (Subcomplex.homOfLE (outerHornCFace_le_C S))).app d).app e q) =
        ((f S).app d).app e q :=
  innerOuterHornCFaceDesc_bidegree m f hf S d e q

end SegalOuterHornCoversTest
