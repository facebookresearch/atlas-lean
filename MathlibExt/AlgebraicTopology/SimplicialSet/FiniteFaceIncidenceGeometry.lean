/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.Data.Finset.Sort
import Mathlib.Order.CompleteLattice.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.RezkFiniteFaceIncidence

/-- The original finite union of selected codimension-one faces of S.
Intersections retain the actual vertex set, not a chosen order of operators. -/
def faceUnion {n : ℕ} (S F : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i ∈ F, stdSimplex.face (S.erase i)

theorem faceUnion_empty {n : ℕ} (S : Finset (Fin (n + 1))) : faceUnion.{u} S ∅ = ⊥ := by
  simp [faceUnion]

/-- The original next face is adjoined to the actual old union. -/
theorem faceUnion_insert {n : ℕ} (S F : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    faceUnion.{u} S (insert j F) = faceUnion S F ⊔ stdSimplex.face (S.erase j) := by
  classical
  simp only [faceUnion, Finset.iSup_insert, sup_comm]

/-- Exact intersection incidence, including repeated omissions and empty
faces. Every inner simplex degree is retained in the equality. -/
theorem faceUnion_inter_next {n : ℕ} (S F : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    faceUnion.{u} S F ⊓ stdSimplex.face (S.erase j) = faceUnion (S.erase j) F := by
  classical
  apply Subfunctor.ext
  funext a
  ext x
  change (x ∈ (⨆ i ∈ F, stdSimplex.face (S.erase i)).obj a ∧
    x ∈ (stdSimplex.face (S.erase j)).obj a) ↔
    x ∈ (⨆ i ∈ F, stdSimplex.face ((S.erase j).erase i)).obj a
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi, hx⟩, hj⟩
    refine ⟨i, hi, ?_⟩
    have hsets : S.erase i ⊓ S.erase j = (S.erase j).erase i := by
      ext v
      simp [and_left_comm]
    rw [← hsets, ← stdSimplex.face_inter_face]
    exact ⟨hx, hj⟩
  · rintro ⟨i, hi, hx⟩
    have hsets : (S.erase j).erase i = S.erase i ⊓ S.erase j := by
      ext v
      simp [and_left_comm]
    rw [hsets, ← stdSimplex.face_inter_face] at hx
    exact ⟨⟨i, hi, hx.1⟩, hx.2⟩

/-- The complete finite face union is the actual simplex boundary. -/
theorem faceUnion_all (n : ℕ) :
    faceUnion.{u} (Finset.univ : Finset (Fin (n + 1))) Finset.univ = boundary n := by
  have erase_univ (i : Fin (n + 1)) :
      (Finset.univ : Finset (Fin (n + 1))).erase i = {i}ᶜ := by
    ext v
    simp [ne_comm]
  simp only [faceUnion, Finset.mem_univ, iSup_pos, erase_univ]
  exact (boundary_eq_iSup n).symm

/-- This exact finite incidence square, not an assumed HC square, is a
pushout on the original face subcomplexes. -/
theorem faceUnion_isPushout {n : ℕ} (S F : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    let sq : Subcomplex.BicartSq (faceUnion.{u} (S.erase j) F) (faceUnion S F)
      (stdSimplex.face (S.erase j)) (faceUnion S (insert j F)) :=
      { inf_eq := faceUnion_inter_next S F j
        sup_eq := (faceUnion_insert S F j).symm }
    IsPushout (Subcomplex.homOfLE sq.le₁₂) (Subcomplex.homOfLE sq.le₁₃)
      (Subcomplex.homOfLE sq.le₂₄) (Subcomplex.homOfLE sq.le₃₄) := by
  let sq : Subcomplex.BicartSq (faceUnion.{u} (S.erase j) F) (faceUnion S F)
      (stdSimplex.face (S.erase j)) (faceUnion S (insert j F)) :=
    { inf_eq := faceUnion_inter_next S F j
      sup_eq := (faceUnion_insert S F j).symm }
  exact sq.isPushout

/-- Tensoring those original incidences with the SAME coefficient row gives
the actual source/target cell-side pushouts used by finite HC induction. -/
theorem faceUnion_tensor_isPushout {n : ℕ} (A : SSet.{u})
    (S F : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    let sq : Subcomplex.BicartSq (faceUnion.{u} (S.erase j) F) (faceUnion S F)
      (stdSimplex.face (S.erase j)) (faceUnion S (insert j F)) :=
      { inf_eq := faceUnion_inter_next S F j
        sup_eq := (faceUnion_insert S F j).symm }
    IsPushout (A ◁ Subcomplex.homOfLE sq.le₁₂) (A ◁ Subcomplex.homOfLE sq.le₁₃)
      (A ◁ Subcomplex.homOfLE sq.le₂₄) (A ◁ Subcomplex.homOfLE sq.le₃₄) := by
  exact (faceUnion_isPushout S F j).map (tensorLeft A)

end SSet.RezkFiniteFaceIncidence
