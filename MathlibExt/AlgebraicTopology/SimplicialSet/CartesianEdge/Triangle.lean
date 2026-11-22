/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SliceComparisonPasting
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Comparison
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
# Composition and cancellation of actual Cartesian edges

For an inner fibration over a quasicategory, an original triangle with
Cartesian final edge has Cartesian initial edge exactly when its long edge
is Cartesian. The full triangle and its original image in the base are
retained. The proof pastes its literal over-slice comparisons and uses the
proved directed face lifting; it makes no right-properness assumption.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace SSet.CartesianEdge

/-- The intrinsic Cartesian condition is the boundary right lifting class of its actual comparison. -/
theorem isPCartesian_iff_rlp_I_comparison {X B : SSet.{u}} (p : X ⟶ B)
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    IsPCartesian p e ↔ modelCategoryQuillen.I.rlp (comparison p e) := by
  constructor
  · intro h A D a ha
    obtain ⟨n⟩ := ha
    exact h n
  · intro h n
    exact h _ (modelCategoryQuillen.boundary_ι_mem_I n)

private theorem middle_vertex_identity :
    stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) :=
  CosimplicialObject.δ_comp_δ (SSet.stdSimplex.{u})
    (n := 0) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)

private theorem final_vertex_identity :
    stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
  (CosimplicialObject.δ_comp_δ (SSet.stdSimplex.{u})
    (n := 0) (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide)).symm

/-- The actual triangle-face composition and cancellation law for Cartesian edges. -/
theorem isPCartesian_face_two_iff_face_one {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] (t : (Δ[2] : SSet.{u}) ⟶ X)
    (h₁₂ : IsPCartesian p (stdSimplex.δ (0 : Fin 3) ≫ t)) :
    IsPCartesian p (stdSimplex.δ (2 : Fin 3) ≫ t) ↔
      IsPCartesian p (stdSimplex.δ (1 : Fin 3) ≫ t) := by
  have hface (i : Fin 3) (hi : i ≠ 0) :
      modelCategoryQuillen.I.rlp (sliceOver.restrictionComparison (stdSimplex.δ i) t p) :=
    sliceOver.rlp_I_restrictionComparison_of_leftAnodyne (stdSimplex.δ i)
      (leftHorn_llp_triangleFace i hi) t p
  have hbase (i : Fin 3) (hi : i ≠ 0) :
      modelCategoryQuillen.I.rlp (sliceOver.restrict B (t ≫ p) (stdSimplex.δ i)) :=
    sliceOver.rlp_I_restrict_of_leftAnodyne B (stdSimplex.δ i)
      (leftHorn_llp_triangleFace i hi) (t ≫ p)
  have hsource : modelCategoryQuillen.I.rlp
      (sliceOver.restrictionComparison (stdSimplex.δ (1 : Fin 2))
        (stdSimplex.δ (0 : Fin 3) ≫ t) p) :=
    sliceOver.rlp_I_restrictionComparison_of_leftAnodyne (stdSimplex.δ (1 : Fin 2))
      leftHorn_llp_source _ p
  rw [isPCartesian_iff_rlp_I_comparison] at h₁₂
  rw [isPCartesian_iff_rlp_I_comparison, isPCartesian_iff_rlp_I_comparison]
  change modelCategoryQuillen.I.rlp
      (sliceOver.restrictionComparison (stdSimplex.δ (0 : Fin 2))
        (stdSimplex.δ (2 : Fin 3) ≫ t) p) ↔
    modelCategoryQuillen.I.rlp
      (sliceOver.restrictionComparison (stdSimplex.δ (0 : Fin 2))
        (stdSimplex.δ (1 : Fin 3) ≫ t) p)
  calc
    _ ↔ modelCategoryQuillen.I.rlp (sliceOver.restrictionComparison
        (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) t p) :=
      (sliceOver.rlp_I_composite_iff_first _ _ t p (hface 2 (by decide))
        (hbase 2 (by decide))).symm
    _ ↔ modelCategoryQuillen.I.rlp (sliceOver.restrictionComparison
        (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) t p) := by
      rw [middle_vertex_identity]
    _ ↔ modelCategoryQuillen.I.rlp (sliceOver.restrictionComparison
        (stdSimplex.δ (0 : Fin 3)) t p) :=
      sliceOver.rlp_I_composite_iff_second _ _ t p hsource
    _ ↔ modelCategoryQuillen.I.rlp (sliceOver.restrictionComparison
        (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) t p) :=
      (sliceOver.rlp_I_composite_iff_second _ _ t p h₁₂).symm
    _ ↔ modelCategoryQuillen.I.rlp (sliceOver.restrictionComparison
        (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)) t p) := by
      rw [final_vertex_identity]
    _ ↔ _ := sliceOver.rlp_I_composite_iff_first _ _ t p (hface 1 (by decide))
      (hbase 1 (by decide))

/-- Composition and cancellation retain the original composition simplex and all its edges. -/
theorem isPCartesian_iff_of_compStruct {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (H : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₁₂ : IsPCartesian p (yonedaEquiv.symm e₁₂.edge)) :
    IsPCartesian p (yonedaEquiv.symm e₀₁.edge) ↔
      IsPCartesian p (yonedaEquiv.symm e₀₂.edge) := by
  have h := isPCartesian_face_two_iff_face_one p (yonedaEquiv.symm H.simplex)
    (by simpa only [stdSimplex.δ_comp_yonedaEquiv_symm, H.d₀] using h₁₂)
  simpa only [stdSimplex.δ_comp_yonedaEquiv_symm, H.d₂, H.d₁] using h

/-- The long original edge of a triangle with both short edges Cartesian is Cartesian. -/
theorem isPCartesian_of_compStruct {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (H : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : IsPCartesian p (yonedaEquiv.symm e₀₁.edge))
    (h₁₂ : IsPCartesian p (yonedaEquiv.symm e₁₂.edge)) :
    IsPCartesian p (yonedaEquiv.symm e₀₂.edge) :=
  (isPCartesian_iff_of_compStruct p H h₁₂).mp h₀₁

end SSet.CartesianEdge
