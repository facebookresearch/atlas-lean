/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RightMappingBoundaryFaces
public import MathlibExt.AlgebraicTopology.SimplicialSet.SliceLeftFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical

/-!
# Actual right mapping spaces preserve genuine trivial fibrations

The complete original boundary and both supplied endpoint maps are lifted
against the actual boundary RLP of the original map. Adding the constant
source face gives the required original simplex, so the same right mapping
map has boundary RLP in every degree. No quasicategory, comparison outcome
or pointwise-to-global strengthening is used.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.mappingSpaceRight
variable {X Y : SSet.{u}} {p : X ⟶ Y}

private theorem yonedaFace {T : SSet.{u}} {n : ℕ}
    (a : Fin (n + 2)) (φ : (Δ[n + 1] : SSet.{u}) ⟶ T) :
    T.δ a (yonedaEquiv φ) = yonedaEquiv (stdSimplex.δ a ≫ φ) :=
  yonedaEquiv_naturality (SimplexCategory.δ a) φ

/-- A true original boundary RLP lifts an entire right-mapping boundary, keeping both individual endpoints
  and the exact original image simplex. -/
theorem exists_lift_boundary_faces (hp : modelCategoryQuillen.I.rlp p)
    (x y : (Δ[0] : SSet.{u}) ⟶ X) {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y))
    (hf : boundary.IsCompatible faces)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ mappingSpaceRight Y (x ≫ p) (y ≫ p))
    (comm : ∀ j : Fin (n + 2), faces j ≫ map X x y p = stdSimplex.δ j ≫ β) :
    ∃ φ : (Δ[n + 1] : SSet.{u}) ⟶ mappingSpaceRight X x y,
      (∀ j : Fin (n + 2), stdSimplex.δ j ≫ φ = faces j) ∧ φ ≫ map X x y p = β := by
  let τY := (simplexEquivSucc Y (x ≫ p) (y ≫ p) (n + 1)) (yonedaEquiv β)
  have hcomm : ∀ j : Fin (n + 3), augmentedFaces x y faces j ≫ p =
      stdSimplex.δ j ≫ τY.val := by
    intro j
    by_cases hj : j = Fin.last (n + 2)
    · subst j
      rw [augmentedFaces_last]
      have hY := (congrArg (fun a : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2] => a ≫ τY.val)
        (frontInclusion_eq (n + 1))).symm.trans τY.2.1
      exact (Category.assoc _ _ _).trans hY.symm
    · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last hj
      rw [augmentedFaces_castSucc]
      have hR : (map X x y p).app (op ⦋n⦌) (yonedaEquiv (faces j)) =
          (mappingSpaceRight Y (x ≫ p) (y ≫ p)).δ j (yonedaEquiv β) := by
        calc
          _ = yonedaEquiv (faces j ≫ map X x y p) := (yonedaEquiv_comp _ _).symm
          _ = yonedaEquiv (stdSimplex.δ j ≫ β) := congrArg yonedaEquiv (comm j)
          _ = _ := (yonedaFace j β).symm
      exact (simplexEquivSucc_map_app_val X x y p n (yonedaEquiv (faces j))).symm.trans
        ((congrArg (fun τ : (mappingSpaceRight Y (x ≫ p) (y ≫ p)) _⦋n⦌ =>
          ((simplexEquivSucc Y (x ≫ p) (y ≫ p) n) τ).val) hR).trans
          (simplexEquivSucc_δ (x ≫ p) (y ≫ p) (yonedaEquiv β) j))
  have hLift : HasLiftingProperty (boundary (n + 2)).ι p :=
    hasLiftingProperty_boundary_of_rlp_I hp (n + 2)
  obtain ⟨σ, hσfaces, hσp⟩ := exists_simplex_lift_boundary
    (augmentedFaces_isCompatible x y faces hf) hLift τY.val hcomm
  have hsource : frontInclusion (n + 1) ≫ σ = toDeltaZero Δ[n + 1] ≫ x := by
    rw [frontInclusion_eq, hσfaces, augmentedFaces_last]
  have htarget : rightVertex (n + 1) ≫ σ = y := by
    rw [← rightVertex_comp_δ_castSucc (0 : Fin (n + 2)), Category.assoc,
      hσfaces, augmentedFaces_castSucc, boundaryFace_target]
  let τX := (simplexEquivSucc X x y (n + 1)).symm ⟨σ, hsource, htarget⟩
  have hτX : ((simplexEquivSucc X x y (n + 1)) τX).val = σ :=
    congrArg Subtype.val ((simplexEquivSucc X x y (n + 1)).apply_symm_apply _)
  have hfaces : ∀ j : Fin (n + 2), (mappingSpaceRight X x y).δ j τX =
      yonedaEquiv (faces j) := by
    intro j
    apply (simplexEquivSucc X x y n).injective
    apply Subtype.ext
    calc
      _ = stdSimplex.δ j.castSucc ≫ ((simplexEquivSucc X x y (n + 1)) τX).val :=
        simplexEquivSucc_δ x y τX j
      _ = stdSimplex.δ j.castSucc ≫ σ := congrArg (fun g => stdSimplex.δ j.castSucc ≫ g) hτX
      _ = augmentedFaces x y faces j.castSucc := hσfaces j.castSucc
      _ = _ := augmentedFaces_castSucc x y faces j
  have himage : (map X x y p).app (op ⦋n + 1⦌) τX = yonedaEquiv β := by
    apply (simplexEquivSucc Y (x ≫ p) (y ≫ p) (n + 1)).injective
    apply Subtype.ext
    exact (simplexEquivSucc_map_app_val X x y p (n + 1) τX).trans
      ((congrArg (fun g => g ≫ p) hτX).trans hσp)
  refine ⟨yonedaEquiv.symm τX, fun j => ?_, ?_⟩
  · apply yonedaEquiv.injective
    exact (yonedaFace j _).symm.trans
      ((congrArg (fun τ => (mappingSpaceRight X x y).δ j τ)
        (yonedaEquiv.apply_symm_apply τX)).trans (hfaces j))
  · apply yonedaEquiv.injective
    exact (yonedaEquiv_comp _ _).trans
      ((congrArg (fun τ => (map X x y p).app (op ⦋n + 1⦌) τ)
        (yonedaEquiv.apply_symm_apply τX)).trans himage)

/-- The actual same-endpoint right mapping map of a genuine trivial fibration is surjective on individual
  original vertices. -/
theorem map_surjective_zero_of_rlp (hp : modelCategoryQuillen.I.rlp p)
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    Function.Surjective ((map X x y p).app (op ⦋0⦌)) := by
  intro β
  let τY := (simplexEquivSucc Y (x ≫ p) (y ≫ p) 0) β
  let faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ X) := fun j => if j = 0 then y else x
  have hcomm : ∀ j : Fin 2, faces j ≫ p = stdSimplex.δ j ≫ τY.val := by
    intro j
    fin_cases j
    · change y ≫ p = stdSimplex.δ (0 : Fin 2) ≫ τY.val
      exact ((congrArg (fun a : (Δ[0] : SSet.{u}) ⟶ Δ[1] => a ≫ τY.val)
        rightVertex_zero).symm.trans τY.2.2).symm
    · change x ≫ p = stdSimplex.δ (1 : Fin 2) ≫ τY.val
      have h := (congrArg (fun a : (Δ[0] : SSet.{u}) ⟶ Δ[1] => a ≫ τY.val)
        (frontInclusion_eq 0)).symm.trans τY.2.1
      have ht : toDeltaZero (Δ[0] : SSet.{u}) ≫ (x ≫ p) = x ≫ p :=
        (congrArg (fun a : (Δ[0] : SSet.{u}) ⟶ Δ[0] => a ≫ (x ≫ p))
          (toDeltaZero_eq (𝟙 (Δ[0] : SSet.{u}))).symm).trans (Category.id_comp _)
      exact (h.trans ht).symm
  obtain ⟨σ, hfaces, hσp⟩ := exists_simplex_lift_boundary
    (show boundary.IsCompatible faces from trivial)
    (hasLiftingProperty_boundary_of_rlp_I hp 1) τY.val hcomm
  have hsource : frontInclusion 0 ≫ σ = toDeltaZero Δ[0] ≫ x := by
    rw [frontInclusion_eq, hfaces]
    change x = toDeltaZero Δ[0] ≫ x
    rw [← toDeltaZero_eq (𝟙 (Δ[0] : SSet.{u})), Category.id_comp]
  have htarget : rightVertex 0 ≫ σ = y := by
    rw [rightVertex_zero, hfaces]
    rfl
  let τX := (simplexEquivSucc X x y 0).symm ⟨σ, hsource, htarget⟩
  refine ⟨τX, ?_⟩
  apply (simplexEquivSucc Y (x ≫ p) (y ≫ p) 0).injective
  apply Subtype.ext
  exact (simplexEquivSucc_map_app_val X x y p 0 τX).trans
    ((congrArg (fun g => g ≫ p)
      (congrArg Subtype.val ((simplexEquivSucc X x y 0).apply_symm_apply _))).trans hσp)

/-- A genuine original trivial fibration induces a genuine trivial Kan fibration on the actual same-endpoint
  right mapping spaces. -/
theorem map_mem_I_rlp (hp : modelCategoryQuillen.I.rlp p)
    (x y : (Δ[0] : SSet.{u}) ⟶ X) : modelCategoryQuillen.I.rlp (map X x y p) := by
  apply (modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary (map X x y p)).mpr
  intro n
  obtain _ | n := n
  · constructor
    intro top bottom sq
    obtain ⟨τ, hτ⟩ := map_surjective_zero_of_rlp hp x y (yonedaEquiv bottom)
    exact ⟨⟨{
      l := yonedaEquiv.symm τ
      fac_left := boundary.hom_ext₀
      fac_right := by
        apply yonedaEquiv.injective
        exact (yonedaEquiv_comp _ _).trans
          ((congrArg (fun t => (map X x y p).app (op ⦋0⦌) t)
            (yonedaEquiv.apply_symm_apply τ)).trans hτ)
    }⟩⟩
  · constructor
    intro top bottom sq
    let faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y) :=
      fun j => boundary.ι j ≫ top
    have hcomm : ∀ j : Fin (n + 2), faces j ≫ map X x y p =
        stdSimplex.δ j ≫ bottom := by
      intro j
      change (boundary.ι j ≫ top) ≫ map X x y p = _
      rw [Category.assoc, sq.w, ← Category.assoc, boundary.ι_ι]
    obtain ⟨φ, hfaces, hφ⟩ := exists_lift_boundary_faces hp x y faces
      (boundary_isCompatible_of_hom top) bottom hcomm
    exact ⟨⟨{
      l := φ
      fac_left := boundary.hom_ext (fun j => by
        rw [← Category.assoc, boundary.ι_ι]
        exact hfaces j)
      fac_right := hφ
    }⟩⟩

end SSet.mappingSpaceRight
