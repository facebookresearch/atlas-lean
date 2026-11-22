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
# Composition and cancellation of actual cocartesian edges

For an inner fibration over a quasicategory, an original triangle with
cocartesian initial edge has cocartesian final edge exactly when its long
edge is cocartesian. The proof retains the full triangle, all three edges
and the original base map, using the actual under-slice comparisons.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- The intrinsic cocartesian condition is boundary lifting of its actual comparison. -/
theorem isPCocartesian_iff_rlp_I_comparison {X B : SSet.{u}} (p : X ⟶ B)
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    IsPCocartesian p e ↔ modelCategoryQuillen.I.rlp (comparison p e) := by
  constructor
  · intro h A D a ha
    obtain ⟨n⟩ := ha
    exact h n
  · intro h n
    exact h _ (modelCategoryQuillen.boundary_ι_mem_I n)

private theorem middle_vertex_identity :
    stdSimplex.δ.{u} (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) :=
  (CosimplicialObject.δ_comp_δ (SSet.stdSimplex.{u})
    (n := 0) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).symm

private theorem initial_vertex_identity :
    stdSimplex.δ.{u} (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
  CosimplicialObject.δ_comp_δ (SSet.stdSimplex.{u})
    (n := 0) (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide)

/-- The original triangle-face composition and cancellation law for cocartesian edges. -/
theorem isPCocartesian_face_zero_iff_face_one {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] (t : (Δ[2] : SSet.{u}) ⟶ X)
    (h₀₁ : IsPCocartesian p (stdSimplex.δ (2 : Fin 3) ≫ t)) :
    IsPCocartesian p (stdSimplex.δ (0 : Fin 3) ≫ t) ↔
      IsPCocartesian p (stdSimplex.δ (1 : Fin 3) ≫ t) := by
  have hface (i : Fin 3) (hi : i ≠ 2) :
      modelCategoryQuillen.I.rlp (sliceUnder.restrictionComparison (stdSimplex.δ i) t p) :=
    sliceUnder.rlp_I_restrictionComparison_of_rightAnodyne (stdSimplex.δ i)
      (rightHorn_llp_triangleFace i hi) t p
  have hbase (i : Fin 3) (hi : i ≠ 2) :
      modelCategoryQuillen.I.rlp (sliceUnder.restrict B (t ≫ p) (stdSimplex.δ i)) :=
    sliceUnder.rlp_I_restrict_of_rightAnodyne B (stdSimplex.δ i)
      (rightHorn_llp_triangleFace i hi) (t ≫ p)
  have htarget : modelCategoryQuillen.I.rlp
      (sliceUnder.restrictionComparison (stdSimplex.δ (0 : Fin 2))
        (stdSimplex.δ (2 : Fin 3) ≫ t) p) :=
    sliceUnder.rlp_I_restrictionComparison_of_rightAnodyne (stdSimplex.δ (0 : Fin 2))
      rightHorn_llp_target _ p
  rw [isPCocartesian_iff_rlp_I_comparison] at h₀₁
  rw [isPCocartesian_iff_rlp_I_comparison, isPCocartesian_iff_rlp_I_comparison]
  change modelCategoryQuillen.I.rlp
      (sliceUnder.restrictionComparison (stdSimplex.δ (1 : Fin 2))
        (stdSimplex.δ (0 : Fin 3) ≫ t) p) ↔
    modelCategoryQuillen.I.rlp
      (sliceUnder.restrictionComparison (stdSimplex.δ (1 : Fin 2))
        (stdSimplex.δ (1 : Fin 3) ≫ t) p)
  calc
    _ ↔ modelCategoryQuillen.I.rlp (sliceUnder.restrictionComparison
        (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) t p) :=
      (sliceUnder.rlp_I_composite_iff_first _ _ t p (hface 0 (by decide))
        (hbase 0 (by decide))).symm
    _ ↔ modelCategoryQuillen.I.rlp (sliceUnder.restrictionComparison
        (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) t p) := by
      rw [middle_vertex_identity]
    _ ↔ modelCategoryQuillen.I.rlp (sliceUnder.restrictionComparison
        (stdSimplex.δ (2 : Fin 3)) t p) :=
      sliceUnder.rlp_I_composite_iff_second _ _ t p htarget
    _ ↔ modelCategoryQuillen.I.rlp (sliceUnder.restrictionComparison
        (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) t p) :=
      (sliceUnder.rlp_I_composite_iff_second _ _ t p h₀₁).symm
    _ ↔ modelCategoryQuillen.I.rlp (sliceUnder.restrictionComparison
        (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)) t p) := by
      rw [initial_vertex_identity]
    _ ↔ _ := sliceUnder.rlp_I_composite_iff_first _ _ t p (hface 1 (by decide))
      (hbase 1 (by decide))

/-- Cocartesian composition and cancellation retain the original composition simplex. -/
theorem isPCocartesian_iff_of_compStruct {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (H : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : IsPCocartesian p (yonedaEquiv.symm e₀₁.edge)) :
    IsPCocartesian p (yonedaEquiv.symm e₁₂.edge) ↔
      IsPCocartesian p (yonedaEquiv.symm e₀₂.edge) := by
  have h := isPCocartesian_face_zero_iff_face_one p (yonedaEquiv.symm H.simplex)
    (by simpa only [stdSimplex.δ_comp_yonedaEquiv_symm, H.d₂] using h₀₁)
  simpa only [stdSimplex.δ_comp_yonedaEquiv_symm, H.d₀, H.d₁] using h

/-- The long original edge is cocartesian when both short original edges are cocartesian. -/
theorem isPCocartesian_of_compStruct {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B] {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (H : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : IsPCocartesian p (yonedaEquiv.symm e₀₁.edge))
    (h₁₂ : IsPCocartesian p (yonedaEquiv.symm e₁₂.edge)) :
    IsPCocartesian p (yonedaEquiv.symm e₀₂.edge) :=
  (isPCocartesian_iff_of_compStruct p H h₀₁).mp h₁₂

end SSet.CocartesianEdge
