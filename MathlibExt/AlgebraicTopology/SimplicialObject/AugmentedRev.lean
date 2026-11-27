/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# Reversal of augmented simplicial objects

This module reverses genuine augmented simplicial objects. The underlying
simplicial object is sent through `SimplicialObject.opFunctor`, so faces and
degeneracies act through reversed indices (`δ i` becomes `δ i.rev`, and
likewise for `σ`). The augmentation point is fixed definitionally, and the
augmentation map agrees with the original pointwise at every simplex.
Applying reversal twice is not the identity by definition; it is related to
the identity by the explicit natural isomorphism `revCompRevIso` (hence the
self-equivalence `revEquivalence`), which is the identity on the
augmentation point.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory
namespace SimplicialObject

variable {C : Type u} [Category.{v} C]

open _root_.SimplicialObject

noncomputable def constOpFunctorObjIso (Q : C) :
    (const C ⋙ opFunctor).obj Q ≅ (const C).obj Q :=
  Iso.refl _

theorem constOpFunctorObjIso_hom_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    (constOpFunctorObjIso (C := C) Q).hom.app Δ = 𝟙 Q :=
  rfl

theorem constOpFunctorObjIso_inv_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    (constOpFunctorObjIso (C := C) Q).inv.app Δ = 𝟙 Q :=
  rfl

noncomputable def constCompOpFunctorIso :
    (const C ⋙ opFunctor) ≅ const C :=
  NatIso.ofComponents (fun Q => constOpFunctorObjIso Q) (by
    intro Q R f
    ext Δ
    dsimp [constOpFunctorObjIso]
    simp [Functor.const, opFunctor])

theorem constCompOpFunctorIso_hom_app_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    ((constCompOpFunctorIso (C := C)).hom.app Q).app Δ = 𝟙 Q :=
  rfl

theorem constCompOpFunctorIso_inv_app_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    ((constCompOpFunctorIso (C := C)).inv.app Q).app Δ = 𝟙 Q :=
  rfl

end SimplicialObject
end CategoryTheory

namespace CategoryTheory
namespace SimplicialObject
namespace Augmented

variable {C : Type u} [Category.{v} C]

open _root_.SimplicialObject

noncomputable def revFunctor : Augmented C ⥤ Augmented C :=
  Comma.map (F₁ := opFunctor (C := C)) (F₂ := 𝟭 C) (F := opFunctor (C := C))
    (Iso.refl _).hom (constCompOpFunctorIso (C := C)).hom

theorem revFunctor_obj_left (X : Augmented C) :
    (revFunctor (C := C).obj X).left = opFunctor.obj X.left :=
  rfl

theorem revFunctor_obj_right (X : Augmented C) :
    (revFunctor (C := C).obj X).right = X.right :=
  rfl

theorem revFunctor_obj_hom (X : Augmented C) :
    (revFunctor (C := C).obj X).hom =
      opFunctor.map X.hom ≫ (constCompOpFunctorIso (C := C)).hom.app X.right := by
  simp [revFunctor]

theorem revFunctor_map_left {X Y : Augmented C} (f : X ⟶ Y) :
    (revFunctor (C := C).map f).left = opFunctor.map f.left :=
  rfl

theorem revFunctor_map_right {X Y : Augmented C} (f : X ⟶ Y) :
    (revFunctor (C := C).map f).right = f.right :=
  rfl

noncomputable def rev (X : Augmented C) : Augmented C :=
  revFunctor.obj X

theorem rev_left (X : Augmented C) :
    (rev (C := C) X).left = opFunctor.obj X.left :=
  rfl

theorem rev_right (X : Augmented C) :
    (rev (C := C) X).right = X.right :=
  rfl

theorem rev_hom (X : Augmented C) :
    (rev (C := C) X).hom =
      opFunctor.map X.hom ≫ (constCompOpFunctorIso (C := C)).hom.app X.right :=
  revFunctor_obj_hom X

theorem rev_hom_app (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (rev (C := C) X).hom.app Δ = X.hom.app Δ := by
  simp [rev_hom, constCompOpFunctorIso_hom_app_app, opFunctor]
  rfl

theorem rev_hom_app_mk (X : Augmented C) (n : ℕ) :
    (rev (C := C) X).hom.app (op (SimplexCategory.mk n)) =
      X.hom.app (op (SimplexCategory.mk n)) :=
  rev_hom_app X _

theorem rev_left_map (X : Augmented C) {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    (rev (C := C) X).left.map f = X.left.map (SimplexCategory.rev.map f.unop).op := by
  dsimp [rev_left, opFunctor]

theorem rev_left_δ (X : Augmented C) {n : ℕ} (i : Fin (n + 2)) :
    (rev (C := C) X).left.δ i = X.left.δ i.rev := by
  simp [SimplicialObject.δ, rev_left_map, SimplexCategory.rev_map_δ]
  rfl

theorem rev_left_σ (X : Augmented C) {n : ℕ} (i : Fin (n + 1)) :
    (rev (C := C) X).left.σ i = X.left.σ i.rev := by
  simp [SimplicialObject.σ, rev_left_map, SimplexCategory.rev_map_σ]
  rfl

noncomputable def revMap {X Y : Augmented C} (f : X ⟶ Y) :
    rev X ⟶ rev Y :=
  revFunctor.map f

theorem revMap_left {X Y : Augmented C} (f : X ⟶ Y) :
    (revMap (C := C) f).left = opFunctor.map f.left :=
  rfl

theorem revMap_right {X Y : Augmented C} (f : X ⟶ Y) :
    (revMap (C := C) f).right = f.right :=
  rfl

theorem revMap_left_app {X Y : Augmented C} (f : X ⟶ Y) (Δ : SimplexCategoryᵒᵖ) :
    (revMap (C := C) f).left.app Δ = f.left.app Δ := by
  dsimp [revMap_left, opFunctor]

noncomputable def revCompRevIsoApp (X : Augmented C) :
    (revFunctor ⋙ revFunctor).obj X ≅ X :=
  Comma.isoMk
    (opFunctorCompOpFunctorIso.app X.left)
    (Iso.refl X.right)
    (by
      ext Δ
      simp only [Functor.id_map]
      have h_left_iso :
          (opFunctorCompOpFunctorIso.hom.app X.left).app Δ =
            𝟙 (X.left.obj Δ) := by
        have h1 : (opFunctorCompOpFunctorIso.hom.app X.left).app Δ =
            (opObjIso (X := opFunctor.obj X.left) (n := Δ)).hom ≫
              (opObjIso (X := X.left) (n := Δ)).hom :=
          opFunctorCompOpFunctorIso_hom_app_app X.left Δ
        have hA : (opObjIso (X := opFunctor.obj X.left) (n := Δ)).hom =
            𝟙 (X.left.obj Δ) := rfl
        have hB : (opObjIso (X := X.left) (n := Δ)).hom =
            𝟙 (X.left.obj Δ) := rfl
        have h2 : (opObjIso (X := opFunctor.obj X.left) (n := Δ)).hom ≫
            (opObjIso (X := X.left) (n := Δ)).hom =
            𝟙 (X.left.obj Δ) ≫ (opObjIso (X := X.left) (n := Δ)).hom :=
          congrArg (· ≫ (opObjIso (X := X.left) (n := Δ)).hom) hA
        have h3 : 𝟙 (X.left.obj Δ) ≫ (opObjIso (X := X.left) (n := Δ)).hom =
            𝟙 (X.left.obj Δ) ≫ 𝟙 (X.left.obj Δ) :=
          congrArg (𝟙 (X.left.obj Δ) ≫ ·) hB
        have h4 : 𝟙 (X.left.obj Δ) ≫ 𝟙 (X.left.obj Δ) = 𝟙 (X.left.obj Δ) := by simp
        exact h1.trans (h2.trans (h3.trans h4))
      have h_double :
          (revFunctor.obj (revFunctor.obj X)).hom.app Δ = X.hom.app Δ :=
        (rev_hom_app (rev (C := C) X) Δ).trans (rev_hom_app X Δ)
      have h_const :
          ((SimplicialObject.const C).map (𝟙 X.right)).app Δ = 𝟙 X.right := by simp
      have h_left_comp :
          (opFunctorCompOpFunctorIso.hom.app X.left ≫ X.hom).app Δ =
            X.hom.app Δ := by
        have h1 : (opFunctorCompOpFunctorIso.hom.app X.left ≫ X.hom).app Δ =
            (opFunctorCompOpFunctorIso.hom.app X.left).app Δ ≫ X.hom.app Δ := rfl
        have h2 : (opFunctorCompOpFunctorIso.hom.app X.left).app Δ ≫ X.hom.app Δ =
            𝟙 (X.left.obj Δ) ≫ X.hom.app Δ :=
          congrArg (· ≫ X.hom.app Δ) h_left_iso
        have h3 : 𝟙 (X.left.obj Δ) ≫ X.hom.app Δ = X.hom.app Δ :=
          Category.id_comp _
        exact h1.trans (h2.trans h3)
      have h_right_comp :
          ((revFunctor.obj (revFunctor.obj X)).hom ≫
              (SimplicialObject.const C).map (𝟙 X.right)).app Δ =
            X.hom.app Δ := by
        have h1 : ((revFunctor.obj (revFunctor.obj X)).hom ≫
            (SimplicialObject.const C).map (𝟙 X.right)).app Δ =
            (revFunctor.obj (revFunctor.obj X)).hom.app Δ ≫
              ((SimplicialObject.const C).map (𝟙 X.right)).app Δ := rfl
        have h2 : (revFunctor.obj (revFunctor.obj X)).hom.app Δ ≫
            ((SimplicialObject.const C).map (𝟙 X.right)).app Δ =
            (revFunctor.obj (revFunctor.obj X)).hom.app Δ ≫ 𝟙 X.right :=
          congrArg ((revFunctor.obj (revFunctor.obj X)).hom.app Δ ≫ ·) h_const
        have h3 : (revFunctor.obj (revFunctor.obj X)).hom.app Δ ≫ 𝟙 X.right =
            (revFunctor.obj (revFunctor.obj X)).hom.app Δ :=
          Category.comp_id _
        exact h1.trans (h2.trans (h3.trans h_double))
      exact h_left_comp.trans h_right_comp.symm)

noncomputable def revCompRevIso : revFunctor ⋙ revFunctor ≅ 𝟭 (Augmented C) :=
  NatIso.ofComponents
    (fun X => revCompRevIsoApp X)
    (fun {X Y} f => by
      apply Comma.hom_ext
      · exact opFunctorCompOpFunctorIso.hom.naturality f.left
      · have h1 : (revFunctor.map (revFunctor.map f)).right = f.right := rfl
        have h2 : (revCompRevIsoApp (C := C) Y).hom.right = 𝟙 Y.right := rfl
        have h3 : (revCompRevIsoApp (C := C) X).hom.right = 𝟙 X.right := rfl
        have h4 : (revFunctor.map (revFunctor.map f)).right ≫ (revCompRevIsoApp Y).hom.right =
            f.right ≫ (revCompRevIsoApp Y).hom.right :=
          congrArg (· ≫ (revCompRevIsoApp Y).hom.right) h1
        have h5 : f.right ≫ (revCompRevIsoApp Y).hom.right =
            f.right ≫ 𝟙 Y.right :=
          congrArg (f.right ≫ ·) h2
        have h6 : f.right ≫ 𝟙 Y.right = f.right :=
          Category.comp_id _
        have h7 : f.right = 𝟙 X.right ≫ f.right :=
          (Category.id_comp _).symm
        have h8 : 𝟙 X.right ≫ f.right =
            (revCompRevIsoApp X).hom.right ≫ f.right :=
          congrArg (· ≫ f.right) h3.symm
        exact h4.trans (h5.trans (h6.trans (h7.trans h8))))

@[simp]
theorem revCompRevIsoApp_hom_left (X : Augmented C) :
    (revCompRevIsoApp (C := C) X).hom.left =
      opFunctorCompOpFunctorIso.hom.app X.left :=
  rfl

@[simp]
theorem revCompRevIsoApp_hom_right (X : Augmented C) :
    (revCompRevIsoApp (C := C) X).hom.right = 𝟙 X.right :=
  rfl

@[simp]
theorem revCompRevIsoApp_inv_left (X : Augmented C) :
    (revCompRevIsoApp (C := C) X).inv.left =
      opFunctorCompOpFunctorIso.inv.app X.left :=
  rfl

@[simp]
theorem revCompRevIsoApp_inv_right (X : Augmented C) :
    (revCompRevIsoApp (C := C) X).inv.right = 𝟙 X.right :=
  rfl

@[simp]
theorem revCompRevIso_hom_left (X : Augmented C) :
    (revCompRevIso (C := C).hom.app X).left =
      opFunctorCompOpFunctorIso.hom.app X.left :=
  rfl

@[simp]
theorem revCompRevIso_hom_right (X : Augmented C) :
    (revCompRevIso (C := C).hom.app X).right = 𝟙 X.right :=
  rfl

@[simp]
theorem revCompRevIso_inv_left (X : Augmented C) :
    (revCompRevIso (C := C).inv.app X).left =
      opFunctorCompOpFunctorIso.inv.app X.left :=
  rfl

@[simp]
theorem revCompRevIso_inv_right (X : Augmented C) :
    (revCompRevIso (C := C).inv.app X).right = 𝟙 X.right :=
  rfl

@[simp]
theorem revCompRevIso_hom_left_app (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (revCompRevIso (C := C).hom.app X).left.app Δ = 𝟙 (X.left.obj Δ) := by
  simp only [revCompRevIso_hom_left,
    opFunctorCompOpFunctorIso_hom_app_app]
  have hA : (opObjIso (X := opFunctor.obj X.left) (n := Δ)).hom =
      𝟙 (X.left.obj Δ) := rfl
  have hB : (opObjIso (X := X.left) (n := Δ)).hom =
      𝟙 (X.left.obj Δ) := rfl
  have h1 : (opObjIso (X := opFunctor.obj X.left) (n := Δ)).hom ≫
      (opObjIso (X := X.left) (n := Δ)).hom =
      𝟙 (X.left.obj Δ) ≫ (opObjIso (X := X.left) (n := Δ)).hom :=
    congrArg (· ≫ (opObjIso (X := X.left) (n := Δ)).hom) hA
  have h2 : 𝟙 (X.left.obj Δ) ≫ (opObjIso (X := X.left) (n := Δ)).hom =
      𝟙 (X.left.obj Δ) ≫ 𝟙 (X.left.obj Δ) :=
    congrArg (𝟙 (X.left.obj Δ) ≫ ·) hB
  have h3 : 𝟙 (X.left.obj Δ) ≫ 𝟙 (X.left.obj Δ) = 𝟙 (X.left.obj Δ) := by simp
  exact h1.trans (h2.trans h3)

@[simp]
theorem revCompRevIso_inv_left_app (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (revCompRevIso (C := C).inv.app X).left.app Δ = 𝟙 (X.left.obj Δ) := by
  simp only [revCompRevIso_inv_left,
    opFunctorCompOpFunctorIso_inv_app_app]
  have hA : (opObjIso (X := X.left) (n := Δ)).inv =
      𝟙 (X.left.obj Δ) := rfl
  have hB : (opObjIso (X := opFunctor.obj X.left) (n := Δ)).inv =
      𝟙 (X.left.obj Δ) := rfl
  have h1 : (opObjIso (X := X.left) (n := Δ)).inv ≫
      (opObjIso (X := opFunctor.obj X.left) (n := Δ)).inv =
      𝟙 (X.left.obj Δ) ≫
        (opObjIso (X := opFunctor.obj X.left) (n := Δ)).inv :=
    congrArg (· ≫ (opObjIso (X := opFunctor.obj X.left) (n := Δ)).inv) hA
  have h2 : 𝟙 (X.left.obj Δ) ≫
      (opObjIso (X := opFunctor.obj X.left) (n := Δ)).inv =
      𝟙 (X.left.obj Δ) ≫ 𝟙 (X.left.obj Δ) :=
    congrArg (𝟙 (X.left.obj Δ) ≫ ·) hB
  have h3 : 𝟙 (X.left.obj Δ) ≫ 𝟙 (X.left.obj Δ) = 𝟙 (X.left.obj Δ) := by simp
  exact h1.trans (h2.trans h3)

theorem revCompRevIso_hom_left_app_mk (X : Augmented C) (n : ℕ) :
    (revCompRevIso (C := C).hom.app X).left.app (op (SimplexCategory.mk n)) =
      𝟙 (X.left.obj (op (SimplexCategory.mk n))) :=
  revCompRevIso_hom_left_app X _

theorem revCompRevIso_inv_left_app_mk (X : Augmented C) (n : ℕ) :
    (revCompRevIso (C := C).inv.app X).left.app (op (SimplexCategory.mk n)) =
      𝟙 (X.left.obj (op (SimplexCategory.mk n))) :=
  revCompRevIso_inv_left_app X _

noncomputable def revEquivalence : Augmented C ≌ Augmented C where
  functor := revFunctor
  inverse := revFunctor
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso
  functor_unitIso_comp X := by
    apply Comma.hom_ext
    · have h_left : (revFunctor.map (revCompRevIso.symm.hom.app X) ≫
            revCompRevIso.hom.app (revFunctor.obj X)).left =
          SimplicialObject.opFunctor.map
            (SimplicialObject.opFunctorCompOpFunctorIso.inv.app X.left) ≫
            SimplicialObject.opFunctorCompOpFunctorIso.hom.app
              (SimplicialObject.opFunctor.obj X.left) := rfl
      rw [h_left]
      exact (SimplicialObject.opEquivalence (C := C)).functor_unitIso_comp X.left
    · have h_eq : (revFunctor.map (revCompRevIso.symm.hom.app X) ≫
            revCompRevIso.hom.app (revFunctor.obj X)).right =
          𝟙 (revFunctor.obj X).right ≫ 𝟙 (revFunctor.obj X).right := rfl
      rw [h_eq]
      simp

end Augmented
end SimplicialObject
end CategoryTheory

end
