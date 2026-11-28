/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosComplex

/-!
# Roos differential and coefficient-map clients

These clients check the covariant coefficient action and minus sign in degree
zero, the projection square of a cochain map, and integer-scalar and
composition laws for the additive coefficient functor.
-/

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosComplexTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Preadditive A]
  [HasProducts.{max u₁ v₁} A]

/-- The native terminal projection with its coefficient target displayed explicitly. -/
private def terminalProjection (M : I ⥤ A) {X Y : I} (f : X ⟶ Y) :
    (∏ᶜ (roosFamily M 0)) ⟶ M.obj Y :=
  Pi.π (roosFamily M 0) ((nerve Iᵒᵖ).δ 1 (ComposableArrows.mk₁ f.op))

/-- Native product coordinates recover the signed action for an actual arrow. -/
example (M : I ⥤ A) {X Y : I} (f : X ⟶ Y) :
    (roosObjIso M 0).inv ≫ (roosComplex M).d 0 1 ≫
        roosπ M (ComposableArrows.mk₁ f.op) =
      Pi.π (roosFamily M 0) ((nerve Iᵒᵖ).δ 0 (ComposableArrows.mk₁ f.op)) ≫
          M.map f -
        terminalProjection M f := by
  fail_if_success
    have : Abelian A := inferInstance
  let F : ComposableArrows Iᵒᵖ 1 := ComposableArrows.mk₁ f.op
  have hface : (CategoryHomology.faceLeftHom (1 : Fin 2) F).unop = 𝟙 Y := by
    rfl
  have hmap : M.map ((CategoryHomology.faceLeftHom (1 : Fin 2) F).unop) =
      𝟙 (M.obj Y) :=
    (congrArg (fun (g : Y ⟶ Y) ↦ M.map g) hface).trans (M.map_id Y)
  let a : (roosCosimplicial M).obj (SimplexCategory.mk 0) ⟶ M.obj Y :=
    roosπ M ((nerve Iᵒᵖ).δ 0 F) ≫ M.map f
  let b : (roosCosimplicial M).obj (SimplexCategory.mk 0) ⟶ M.obj Y :=
    roosπ M ((nerve Iᵒᵖ).δ 1 F) ≫
      M.map ((CategoryHomology.faceLeftHom (1 : Fin 2) F).unop)
  have hd : (roosComplex M).d 0 1 ≫ roosπ M F = a - b :=
    roosComplex_d_zero_π M F
  have h := congrArg
    (fun (k : (roosCosimplicial M).obj (SimplexCategory.mk 0) ⟶ M.obj Y) ↦
      (roosObjIso M 0).inv ≫ k) hd
  have hfirst := roosObjIso_inv_π M ((nerve Iᵒᵖ).δ 0 F)
  have hlastπ : (roosObjIso M 0).inv ≫ roosπ M ((nerve Iᵒᵖ).δ 1 F) =
      terminalProjection M f := roosObjIso_inv_π M ((nerve Iᵒᵖ).δ 1 F)
  have ha : (roosObjIso M 0).inv ≫ a =
      Pi.π (roosFamily M 0) ((nerve Iᵒᵖ).δ 0 F) ≫ M.map f :=
    (Category.assoc (roosObjIso M 0).inv
      (roosπ M ((nerve Iᵒᵖ).δ 0 F)) (M.map f)).symm.trans
        (congrArg (fun (k : (∏ᶜ (roosFamily M 0)) ⟶ M.obj X) ↦ k ≫ M.map f) hfirst)
  have hb : (roosObjIso M 0).inv ≫ b = terminalProjection M f :=
    (Category.assoc (roosObjIso M 0).inv (roosπ M ((nerve Iᵒᵖ).δ 1 F))
      (M.map ((CategoryHomology.faceLeftHom (1 : Fin 2) F).unop))).symm.trans
        ((congrArg
          (fun (k : (∏ᶜ (roosFamily M 0)) ⟶ M.obj Y) ↦
            k ≫ M.map ((CategoryHomology.faceLeftHom (1 : Fin 2) F).unop)) hlastπ).trans
          ((congrArg (fun (g : M.obj Y ⟶ M.obj Y) ↦ terminalProjection M f ≫ g)
            hmap).trans (Category.comp_id _)))
  exact h.trans ((Preadditive.comp_sub (roosObjIso M 0).inv a b).trans
    (congrArg₂ (fun (p q : (∏ᶜ (roosFamily M 0)) ⟶ M.obj Y) ↦ p - q) ha hb))

/-- The actual cochain map commutes with the actual differential after projection. -/
example {M N : I ⥤ A} (α : M ⟶ N)
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk 1))) :
    ((roosComplexFunctor (I := I) (A := A)).map α).f 0 ≫
        (roosComplex N).d 0 1 ≫ roosπ N F =
      (roosComplex M).d 0 1 ≫ roosπ M F ≫ α.app (F.left.unop) := by
  have hcomm :
      ((roosComplexFunctor (I := I) (A := A)).map α).f 0 ≫
          (roosComplex N).d 0 1 =
        (roosComplex M).d 0 1 ≫
          ((roosComplexFunctor (I := I) (A := A)).map α).f 1 :=
    ((roosComplexFunctor (I := I) (A := A)).map α).comm 0 1
  have h := congrArg
    (fun (k : (roosCosimplicial M).obj (SimplexCategory.mk 0) ⟶
      (roosCosimplicial N).obj (SimplexCategory.mk 1)) ↦ k ≫ roosπ N F) hcomm
  have hp := congrArg
    (fun (k : (roosComplex M).X 1 ⟶ N.obj (F.left.unop)) ↦ (roosComplex M).d 0 1 ≫ k)
    (roosComplexFunctor_map_f_π α F)
  exact (Category.assoc (((roosComplexFunctor (I := I) (A := A)).map α).f 0)
    ((roosComplex N).d 0 1) (roosπ N F)).symm.trans
      (h.trans ((Category.assoc ((roosComplex M).d 0 1)
        (((roosComplexFunctor (I := I) (A := A)).map α).f 1) (roosπ N F)).trans hp))

/-- Integer scaling is supplied by the proved additive instance on the actual maps. -/
example {M N : I ⥤ A} (α : M ⟶ N) (r : ℤ) {n : ℕ}
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    ((roosComplexFunctor (I := I) (A := A)).map (r • α)).f n ≫ roosπ N F =
      r • (roosπ M F ≫ α.app (F.left.unop)) := by
  have hscale := congrArg
    (fun (g : roosComplex M ⟶ roosComplex N) ↦ g.f n)
    (Functor.map_zsmul (roosComplexFunctor (I := I) (A := A)) (f := α) (r := r))
  have hs : ((roosComplexFunctor (I := I) (A := A)).map (r • α)).f n =
      r • ((roosComplexFunctor (I := I) (A := A)).map α).f n :=
    hscale.trans (HomologicalComplex.zsmul_f_apply r _ n)
  have h := congrArg
    (fun (k : (roosComplex M).X n ⟶ (roosComplex N).X n) ↦ k ≫ roosπ N F) hs
  exact h.trans ((Preadditive.zsmul_comp
    (((roosComplexFunctor (I := I) (A := A)).map α).f n) (roosπ N F) r).trans
      (congrArg (fun (k : (roosComplex M).X n ⟶ N.obj (F.left.unop)) ↦ r • k)
        (roosComplexFunctor_map_f_π α F)))

/-- Composition uses the native higher maps of both coefficient transformations. -/
example {M N P : I ⥤ A} (α : M ⟶ N) (β : N ⟶ P) {n : ℕ}
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    ((roosComplexFunctor (I := I) (A := A)).map (α ≫ β)).f n ≫ roosπ P F =
      roosπ M F ≫ α.app (F.left.unop) ≫ β.app (F.left.unop) := by
  simpa only [NatTrans.comp_app] using roosComplexFunctor_map_f_π (α ≫ β) F

end RoosComplexTests

end
