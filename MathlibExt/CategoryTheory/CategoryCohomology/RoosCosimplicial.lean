/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFunctoriality
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# The Roos cosimplicial object

Let I be a category and M : I → A a covariant coefficient diagram. Sized
products in A give the Roos cosimplicial object, whose factors are indexed by
weak composable-arrow chains and carry the coefficient at the terminal
object. Its cofaces, codegeneracies and coefficient maps are characterized by
product projections. The index and both coefficient-category universes are
independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A]
  [HasProducts.{max u₁ v₁} A]

/-- The full weak-chain Roos cosimplicial object. -/
abbrev roosCosimplicial (M : I ⥤ A) : CosimplicialObject A :=
  (coefficientBarSimplicial M.op).unop

/-- The coefficient family on chains displayed as `iₙ → … → i₀` in `I`. -/
def roosFamily (M : I ⥤ A) (n : ℕ) : ComposableArrows Iᵒᵖ n → A :=
  fun F ↦ M.obj (F.left.unop)

/-- The canonical product coordinates of the degree object. -/
def roosObjIso (M : I ⥤ A) (n : ℕ) :
    (roosCosimplicial M).obj (SimplexCategory.mk n) ≅ ∏ᶜ (roosFamily M n) :=
  (opProductIsoCoproduct (roosFamily M n)).unop

/-- The projection to the terminal coefficient of a weak chain. -/
abbrev roosπ (M : I ⥤ A) {n : ℕ} (F : ComposableArrows Iᵒᵖ n) :
    (roosCosimplicial M).obj (SimplexCategory.mk n) ⟶ M.obj (F.left.unop) :=
  (coefficientBarι M.op F).unop

/-- The product comparison identifies its projection with `roosπ`. -/
@[reassoc (attr := simp)]
theorem roosObjIso_hom_π (M : I ⥤ A) {n : ℕ}
    (F : ComposableArrows Iᵒᵖ n) :
    (roosObjIso M n).hom ≫ Pi.π (roosFamily M n) F = roosπ M F := by
  exact congrArg Quiver.Hom.unop
    (π_comp_opProductIsoCoproduct_hom (roosFamily M n) F)

/-- The inverse product comparison recovers each weak-chain projection. -/
@[reassoc (attr := simp)]
theorem roosObjIso_inv_π (M : I ⥤ A) {n : ℕ}
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    (roosObjIso M n).inv ≫ roosπ M F = Pi.π (roosFamily M n) F := by
  exact (Iso.inv_comp_eq (roosObjIso M n)).mpr (roosObjIso_hom_π M F).symm

/-- Morphisms into a Roos degree object are determined by its projections. -/
theorem roos_hom_ext (M : I ⥤ A) {n : ℕ} {Z : A}
    {f g : Z ⟶ (roosCosimplicial M).obj (SimplexCategory.mk n)}
    (h : ∀ F : ComposableArrows Iᵒᵖ n, f ≫ roosπ M F = g ≫ roosπ M F) :
    f = g := by
  apply (cancel_mono (roosObjIso M n).hom).1
  apply Pi.hom_ext
  intro F
  rw [Category.assoc, roosObjIso_hom_π, Category.assoc, roosObjIso_hom_π]
  exact h F

/-- A coefficient transformation induces an cosimplicial map. -/
def roosMap {M N : I ⥤ A} (α : M ⟶ N) :
    roosCosimplicial M ⟶ roosCosimplicial N :=
  NatTrans.unop (coefficientBarSimplicialMap (NatTrans.op α))

/-- The full Roos construction is covariant in its coefficient diagram. -/
abbrev roosCosimplicialFunctor : (I ⥤ A) ⥤ CosimplicialObject A where
  obj := roosCosimplicial
  map := roosMap
  map_id M := by
    change NatTrans.unop
      ((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map
        (NatTrans.op (𝟙 M))) = _
    rw [NatTrans.op_id, Functor.map_id, NatTrans.unop_id]
    simp [roosCosimplicial]
  map_comp α β := by
    change NatTrans.unop
      ((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map
        (NatTrans.op (α ≫ β))) =
      NatTrans.unop
        ((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map
          (NatTrans.op α)) ≫
      NatTrans.unop
        ((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map
          (NatTrans.op β))
    rw [NatTrans.op_comp, Functor.map_comp, NatTrans.unop_comp]

/-- The Roos cosimplicial functor assigns the Roos cosimplicial object to a coefficient diagram. -/
@[simp]
theorem roosCosimplicialFunctor_obj (M : I ⥤ A) :
    (roosCosimplicialFunctor (I := I) (A := A)).obj M = roosCosimplicial M := rfl

/-- A coefficient natural transformation induces its corresponding Roos cosimplicial morphism. -/
@[simp]
theorem roosCosimplicialFunctor_map {M N : I ⥤ A} (α : M ⟶ N) :
    (roosCosimplicialFunctor (I := I) (A := A)).map α = roosMap α := rfl

/-- Coefficient maps act by the component on each weak-chain factor. -/
@[reassoc (attr := simp)]
theorem roosMap_app_π {M N : I ⥤ A} (α : M ⟶ N) {n : ℕ}
    (F : ComposableArrows Iᵒᵖ n) :
    (roosMap α).app (SimplexCategory.mk n) ≫ roosπ N F =
      roosπ M F ≫ α.app (F.left.unop) := by
  change (coefficientBarMap (NatTrans.op α) n).unop ≫
      (coefficientBarι N.op F).unop =
    (coefficientBarι M.op F).unop ≫ α.app (F.left.unop)
  exact congrArg Quiver.Hom.unop (coefficientBarι_map (NatTrans.op α) F)

/-- A coface deletes a vertex, applying the endpoint coefficient map. -/
@[reassoc]
theorem roos_coface_π (M : I ⥤ A) {n : ℕ} (i : Fin (n + 2))
    (F : ComposableArrows Iᵒᵖ (n + 1)) :
    (roosCosimplicial M).map (SimplexCategory.δ i) ≫ roosπ M F =
      roosπ M ((nerve Iᵒᵖ).δ i F) ≫ M.map ((faceLeftHom i F).unop) := by
  change ((coefficientBarSimplicial M.op).map (SimplexCategory.δ i).op).unop ≫
      (coefficientBarι M.op F).unop = _
  rw [coefficientBarSimplicial_map_δ]
  exact congrArg Quiver.Hom.unop (coefficientBarι_face M.op i F)

/-- The zeroth coface uses the arrow from the old second object to its terminal object. -/
@[reassoc]
theorem roos_coface_zero_π (M : I ⥤ A) {n : ℕ}
    (F : ComposableArrows Iᵒᵖ (n + 1)) :
    (roosCosimplicial M).map (SimplexCategory.δ (0 : Fin (n + 2))) ≫ roosπ M F =
      roosπ M ((nerve Iᵒᵖ).δ 0 F) ≫ M.map ((F.map' 0 1).unop) := by
  rw [roos_coface_π, faceLeftHom_zero]
  rfl

/-- A codegeneracy projects to the weak chain with the chosen identity inserted. -/
@[reassoc]
theorem roos_codegeneracy_π (M : I ⥤ A) {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows Iᵒᵖ n) :
    (roosCosimplicial M).map (SimplexCategory.σ i) ≫ roosπ M F =
      roosπ M ((nerve Iᵒᵖ).σ i F) ≫ M.map ((degeneracyLeftHom i F).unop) := by
  change ((coefficientBarSimplicial M.op).map (SimplexCategory.σ i).op).unop ≫
      (coefficientBarι M.op F).unop = _
  rw [coefficientBarSimplicial_map_σ]
  exact congrArg Quiver.Hom.unop (coefficientBarι_degeneracy M.op i F)

end CategoryTheory.CategoryCohomology

end
