/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosCosimplicial

/-!
# Roos product-coordinate clients

A nonconstant arrow diagram distinguishes coefficient action at the first
coface from identity transport at the last coface. Product projections also
check the covariant direction of coefficient maps in a general coefficient
category with sized products.
-/

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosCosimplicialTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A]
  [HasProducts.{max u₁ v₁} A]

/-- A nonconstant arrow diagram uses its structure map at the first coface. -/
example (M : I ⥤ A) {X Y : I} (f : X ⟶ Y) :
    (roosCosimplicial M).map (SimplexCategory.δ (0 : Fin 2)) ≫
        roosπ M (ComposableArrows.mk₁ f.op) =
      roosπ M ((nerve Iᵒᵖ).δ 0 (ComposableArrows.mk₁ f.op)) ≫ M.map f := by
  fail_if_success
    have : HasZeroMorphisms A := inferInstance
  exact roos_coface_zero_π M (ComposableArrows.mk₁ f.op)

/-- The other face of that same arrow leaves the terminal coefficient unchanged. -/
example (M : I ⥤ A) {X Y : I} (f : X ⟶ Y) :
    (roosCosimplicial M).map (SimplexCategory.δ (1 : Fin 2)) ≫
        roosπ M (ComposableArrows.mk₁ f.op) =
      roosπ M ((nerve Iᵒᵖ).δ 1 (ComposableArrows.mk₁ f.op)) := by
  let F : ComposableArrows Iᵒᵖ 1 := ComposableArrows.mk₁ f.op
  have hface : (CategoryHomology.faceLeftHom (1 : Fin 2) F).unop = 𝟙 Y := by
    rfl
  have hmap : M.map ((CategoryHomology.faceLeftHom (1 : Fin 2) F).unop) =
      𝟙 (M.obj Y) :=
    (congrArg (fun (g : Y ⟶ Y) ↦ M.map g) hface).trans (M.map_id Y)
  exact (roos_coface_π M (1 : Fin 2) F).trans
    ((congrArg
      (fun (g : M.obj Y ⟶ M.obj Y) ↦ roosπ M ((nerve Iᵒᵖ).δ 1 F) ≫ g)
      hmap).trans (Category.comp_id _))

/-- Inserting the identity of an actual object gives the weak degree-one factor. -/
example (M : I ⥤ A) (X : I) :
    (roosCosimplicial M).map (SimplexCategory.σ (0 : Fin 1)) ≫
        roosπ M (ComposableArrows.mk₀ (op X)) =
      roosπ M ((nerve Iᵒᵖ).σ 0 (ComposableArrows.mk₀ (op X))) := by
  let F : ComposableArrows Iᵒᵖ 0 := ComposableArrows.mk₀ (op X)
  have hdeg : (CategoryHomology.degeneracyLeftHom (0 : Fin 1) F).unop = 𝟙 X := by
    rfl
  have hmap : M.map ((CategoryHomology.degeneracyLeftHom (0 : Fin 1) F).unop) =
      𝟙 (M.obj X) :=
    (congrArg (fun (g : X ⟶ X) ↦ M.map g) hdeg).trans (M.map_id X)
  exact (roos_codegeneracy_π M (0 : Fin 1) F).trans
    ((congrArg
      (fun (g : M.obj X ⟶ M.obj X) ↦ roosπ M ((nerve Iᵒᵖ).σ 0 F) ≫ g)
      hmap).trans (Category.comp_id _))

/-- Starting in native product coordinates preserves the forward coefficient map. -/
example {M N : I ⥤ A} (α : M ⟶ N) {n : ℕ}
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    (roosObjIso M n).inv ≫ (roosMap α).app (SimplexCategory.mk n) ≫ roosπ N F =
      Pi.π (roosFamily M n) F ≫ α.app (F.left.unop) := by
  have h := congrArg
    (fun (k : (roosCosimplicial M).obj (SimplexCategory.mk n) ⟶
      N.obj (F.left.unop)) ↦ (roosObjIso M n).inv ≫ k)
    (roosMap_app_π α F)
  calc
    (roosObjIso M n).inv ≫ (roosMap α).app (SimplexCategory.mk n) ≫ roosπ N F =
        (roosObjIso M n).inv ≫ (roosπ M F ≫ α.app (F.left.unop)) := h
    _ = ((roosObjIso M n).inv ≫ roosπ M F) ≫ α.app (F.left.unop) :=
      (Category.assoc _ _ _).symm
    _ = Pi.π (roosFamily M n) F ≫ α.app (F.left.unop) :=
      congrArg
        (fun (k : (∏ᶜ (roosFamily M n)) ⟶ M.obj (F.left.unop)) ↦
          k ≫ α.app (F.left.unop)) (roosObjIso_inv_π M F)

end RoosCosimplicialTests

end
