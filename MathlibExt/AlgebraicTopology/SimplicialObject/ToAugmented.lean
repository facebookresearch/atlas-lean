/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.DataAugmented
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Augmented data to augmented simplicial objects

Functorial conversion from augmented simplicial data to genuine augmented
simplicial objects via `Data.Augmented.toSimplicialAugmented` and
`Data.Augmented.toSimplicialFunctor`. The left component is the transported
underlying data, the point is unchanged, and the augmentation map is the
transported data morphism followed by `constFunctorIso`. Computation lemmas
expose the left, right, and hom components. Comma-category orientation keeps
the diagram on the left and the point on the right.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory

namespace SimplicialObject

namespace Data

variable {C : Type u} [Category.{v} C]

@[simp]
theorem constData_toOpFunctor_map_δ (Q : C) {n : ℕ} (i : Fin (n + 2)) :
    (constData (C := C) Q).toOpFunctor.map (SimplexCategoryGenRel.δ i) = 𝟙 _ := by
  simp [toOpFunctor_map_δ]

@[simp]
theorem constData_toOpFunctor_map_σ (Q : C) {n : ℕ} (i : Fin (n + 1)) :
    (constData (C := C) Q).toOpFunctor.map (SimplexCategoryGenRel.σ i) = 𝟙 _ := by
  simp [toOpFunctor_map_σ]

theorem constData_toOpFunctor_map (Q : C) {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    (constData (C := C) Q).toOpFunctor.map f = 𝟙 _ := by
  induction f using SimplexCategoryGenRel.hom_induction with
  | id => simp
  | comp_δ _ i ih => simp [Functor.map_comp, ih, constData_toOpFunctor_map_δ]
  | comp_σ _ i ih => simp [Functor.map_comp, ih, constData_toOpFunctor_map_σ]

@[simp]
theorem constData_toGenRelFunctor_map_δ_op (Q : C) {n : ℕ} (i : Fin (n + 2)) :
    (constData (C := C) Q).toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op = 𝟙 _ := by
  simp [toGenRelFunctor_map_δ_op]

@[simp]
theorem constData_toGenRelFunctor_map_σ_op (Q : C) {n : ℕ} (i : Fin (n + 1)) :
    (constData (C := C) Q).toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op = 𝟙 _ := by
  simp [toGenRelFunctor_map_σ_op]

theorem constData_toGenRelFunctor_map_op (Q : C) {a b : SimplexCategoryGenRel}
    (f : a ⟶ b) :
    (constData (C := C) Q).toGenRelFunctor.map f.op = 𝟙 _ := by
  induction f using SimplexCategoryGenRel.hom_induction with
  | id => simp
  | comp_δ _ i ih =>
    rw [op_comp, Functor.map_comp]
    simp [ih, constData_toGenRelFunctor_map_δ_op]
  | comp_σ _ i ih =>
    rw [op_comp, Functor.map_comp]
    simp [ih, constData_toGenRelFunctor_map_σ_op]

theorem constData_toGenRelFunctor_map (Q : C) {A B : SimplexCategoryGenRelᵒᵖ}
    (f : A ⟶ B) :
    (constData (C := C) Q).toGenRelFunctor.map f = 𝟙 _ := by
  have h : f = f.unop.op := (Quiver.Hom.op_unop f).symm
  rw [h]
  exact constData_toGenRelFunctor_map_op Q f.unop

theorem constData_toSimplicialObject_map (Q : C) {X Y : SimplexCategoryᵒᵖ}
    (f : X ⟶ Y) :
    (constData (C := C) Q).toSimplicialObject.map f = 𝟙 _ := by
  have h : (constData Q).toSimplicialObject.map f =
      (constData Q).toGenRelFunctor.map (SimplexCategoryGenRel.fromSimplexCategory.op.map f) := rfl
  rw [h]
  exact constData_toGenRelFunctor_map Q _

@[simp]
theorem constData_toSimplicialObject_map_δ (Q : C) {n : ℕ} (i : Fin (n + 2)) :
    (constData (C := C) Q).toSimplicialObject.map (SimplexCategory.δ i).op = 𝟙 _ := by
  simp [constData_toSimplicialObject_map]

@[simp]
theorem constData_toSimplicialObject_map_σ (Q : C) {n : ℕ} (i : Fin (n + 1)) :
    (constData (C := C) Q).toSimplicialObject.map (SimplexCategory.σ i).op = 𝟙 _ := by
  simp [constData_toSimplicialObject_map]

noncomputable def constDataIso (Q : C) :
    (constData (C := C) Q).toSimplicialObject ≅ (SimplicialObject.const C).obj Q := by
  refine NatIso.ofComponents (fun _ => Iso.refl Q) ?_
  intro X Y f
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  have hEq : (constData Q).toSimplicialObject.obj (op X) = Q := by
    simp [toSimplicialObject_obj]
  have hMap : (constData Q).toSimplicialObject.map f = 𝟙 _ :=
    constData_toSimplicialObject_map Q f
  have h1 : (constData Q).toSimplicialObject.map f = 𝟙 Q := by
    cases hEq
    exact hMap
  have hG : ((SimplicialObject.const C).obj Q).map f = 𝟙 Q := rfl
  simp only [h1, hG]
  rfl

@[simp]
theorem constDataIso_hom_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    (constDataIso (C := C) Q).hom.app Δ = 𝟙 Q :=
  rfl

@[simp]
theorem constDataIso_inv_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    (constDataIso (C := C) Q).inv.app Δ = 𝟙 Q :=
  rfl

@[simp]
theorem constDataIso_hom_app_mk (Q : C) (n : ℕ) :
    (constDataIso (C := C) Q).hom.app (op (SimplexCategory.mk n)) = 𝟙 Q :=
  rfl

@[simp]
theorem constDataIso_inv_app_mk (Q : C) (n : ℕ) :
    (constDataIso (C := C) Q).inv.app (op (SimplexCategory.mk n)) = 𝟙 Q :=
  rfl

noncomputable def constFunctorIsoAux (Q : C) :
    (constFunctor (C := C) ⋙ toSimplicialFunctor).obj Q ≅ (SimplicialObject.const C).obj Q := by
  refine NatIso.ofComponents (fun _ => Iso.refl Q) ?_
  intro X Y f
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  have hEq : ((constFunctor ⋙ toSimplicialFunctor).obj Q) = (constData Q).toSimplicialObject := rfl
  have h1 : ((constFunctor ⋙ toSimplicialFunctor).obj Q).map f = 𝟙 Q := by
    cases hEq
    have hMap : (constData Q).toSimplicialObject.map f = 𝟙 _ :=
      constData_toSimplicialObject_map Q f
    have hObj : (constData Q).toSimplicialObject.obj (op X) = Q := by
      simp [toSimplicialObject_obj]
    cases hObj
    exact hMap
  have hG : ((SimplicialObject.const C).obj Q).map f = 𝟙 Q := rfl
  simp only [h1, hG]
  rfl

noncomputable def constFunctorIso :
    (constFunctor (C := C) ⋙ toSimplicialFunctor) ≅ SimplicialObject.const C := by
  refine NatIso.ofComponents (fun Q => constFunctorIsoAux Q) ?_
  intro Q R f
  ext Δ
  obtain ⟨Δ⟩ := Δ
  have h1 : ((constFunctor ⋙ toSimplicialFunctor).map f ≫ (constFunctorIsoAux R).hom).app (op Δ) =
      f ≫ 𝟙 R := rfl
  have h2 : f ≫ 𝟙 R = f := by simp
  have h3 : f = 𝟙 Q ≫ f := by simp
  have h4 : 𝟙 Q ≫ f = ((constFunctorIsoAux Q).hom ≫ (const C).map f).app (op Δ) := rfl
  exact h1.trans (h2.trans (h3.trans h4))

@[simp]
theorem constFunctorIso_hom_app (Q : C) :
    (constFunctorIso (C := C)).hom.app Q = (constDataIso Q).hom := by
  ext Δ
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem constFunctorIso_inv_app (Q : C) :
    (constFunctorIso (C := C)).inv.app Q = (constDataIso Q).inv := by
  ext Δ
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem constFunctorIso_hom_app_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    ((constFunctorIso (C := C)).hom.app Q).app Δ = 𝟙 Q := by
  rfl

@[simp]
theorem constFunctorIso_inv_app_app (Q : C) (Δ : SimplexCategoryᵒᵖ) :
    ((constFunctorIso (C := C)).inv.app Q).app Δ = 𝟙 Q := by
  rfl

@[simp]
theorem constFunctorIso_hom_app_mk (Q : C) (n : ℕ) :
    ((constFunctorIso (C := C)).hom.app Q).app (op (SimplexCategory.mk n)) = 𝟙 Q := by
  rfl

@[simp]
theorem constFunctorIso_inv_app_mk (Q : C) (n : ℕ) :
    ((constFunctorIso (C := C)).inv.app Q).app (op (SimplexCategory.mk n)) = 𝟙 Q := by
  rfl

end Data

namespace Data

namespace Augmented

variable {C : Type u} [Category.{v} C]

/--
Transport an augmented simplicial data object to a augmented simplicial object. The left object is
`Data.toSimplicialObject`, the point is unchanged, and the augmentation is the transported data
morphism followed by the `constFunctorIso` comparison.
-/
noncomputable def toSimplicialAugmented (A : Augmented C) :
    SimplicialObject.Augmented C where
  left := (drop.obj A).toSimplicialObject
  right := point.obj A
  hom :=
    toSimplicialNatTrans ((A : Comma (𝟭 (Data C)) (constFunctor (C := C))).hom) ≫
      (constFunctorIso (C := C)).hom.app (point.obj A)

@[simp]
theorem toSimplicialAugmented_left (A : Augmented C) :
    (toSimplicialAugmented A).left = (drop.obj A).toSimplicialObject :=
  rfl

@[simp]
theorem toSimplicialAugmented_right (A : Augmented C) :
    (toSimplicialAugmented A).right = point.obj A :=
  rfl

@[simp]
theorem toSimplicialAugmented_drop_obj (A : Augmented C) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented A)) =
      (drop.obj A).toSimplicialObject :=
  rfl

@[simp]
theorem toSimplicialAugmented_point_obj (A : Augmented C) :
    (SimplicialObject.Augmented.point.obj (toSimplicialAugmented A)) = point.obj A :=
  rfl

@[simp]
theorem toSimplicialAugmented_hom (A : Augmented C) :
    (toSimplicialAugmented A).hom =
      toSimplicialNatTrans ((A : Comma (𝟭 (Data C)) (constFunctor (C := C))).hom) ≫
        (constFunctorIso (C := C)).hom.app (point.obj A) :=
  rfl

@[simp]
theorem toSimplicialAugmented_obj_mk (A : Augmented C) (n : ℕ) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented A)).obj
        (op (SimplexCategory.mk n)) =
      (drop.obj A).obj n :=
  rfl

theorem toSimplicialAugmented_obj (A : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented A)).obj Δ =
      (drop.obj A).obj (unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem toSimplicialAugmented_left_obj_mk (A : Augmented C) (n : ℕ) :
    (toSimplicialAugmented A).left.obj (op (SimplexCategory.mk n)) =
      (drop.obj A).obj n :=
  rfl

theorem toSimplicialAugmented_left_obj (A : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialAugmented A).left.obj Δ =
      (drop.obj A).obj (unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem toSimplicialAugmented_hom_app_mk (A : Augmented C) (n : ℕ) :
    (toSimplicialAugmented A).hom.app (op (SimplexCategory.mk n)) =
      ((A : Comma (𝟭 (Data C)) (constFunctor (C := C))).hom).app n := by
  have h :
      (toSimplicialAugmented A).hom.app (op (SimplexCategory.mk n)) =
        (toSimplicialNatTrans ((A : Comma (𝟭 (Data C)) (constFunctor (C := C))).hom)).app
            (op (SimplexCategory.mk n)) ≫
          ((constFunctorIso (C := C)).hom.app (point.obj A)).app
            (op (SimplexCategory.mk n)) :=
    rfl
  rw [h, toSimplicialNatTrans_app_mk, constFunctorIso_hom_app_mk]
  exact Category.comp_id _

theorem toSimplicialAugmented_hom_app (A : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialAugmented A).hom.app Δ =
      ((A : Comma (𝟭 (Data C)) (constFunctor (C := C))).hom).app (unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  have h :
      (toSimplicialAugmented A).hom.app (op Δ) =
        (toSimplicialNatTrans ((A : Comma (𝟭 (Data C)) (constFunctor (C := C))).hom)).app (op Δ) ≫
          ((constFunctorIso (C := C)).hom.app (point.obj A)).app (op Δ) :=
    rfl
  rw [h, toSimplicialNatTrans_app, constFunctorIso_hom_app_app]
  exact Category.comp_id _

@[simp]
theorem toSimplicialAugmented_left_map_δ (A : Augmented C) {n : ℕ}
    (i : Fin (n + 2)) :
    (toSimplicialAugmented A).left.map (SimplexCategory.δ i).op =
      (drop.obj A).δ i :=
  toSimplicialObject_map_δ (drop.obj A) i

@[simp]
theorem toSimplicialAugmented_left_map_σ (A : Augmented C) {n : ℕ}
    (i : Fin (n + 1)) :
    (toSimplicialAugmented A).left.map (SimplexCategory.σ i).op =
      (drop.obj A).σ i :=
  toSimplicialObject_map_σ (drop.obj A) i

@[simp]
theorem toSimplicialAugmented_drop_map_δ (A : Augmented C) {n : ℕ}
    (i : Fin (n + 2)) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented A)).map
        (SimplexCategory.δ i).op =
      (drop.obj A).δ i :=
  toSimplicialObject_map_δ (drop.obj A) i

@[simp]
theorem toSimplicialAugmented_drop_map_σ (A : Augmented C) {n : ℕ}
    (i : Fin (n + 1)) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented A)).map
        (SimplexCategory.σ i).op =
      (drop.obj A).σ i :=
  toSimplicialObject_map_σ (drop.obj A) i

theorem toSimplicialAugmented_left_δ (A : Augmented C) {n : ℕ}
    (i : Fin (n + 2)) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented A)).δ i =
      (drop.obj A).δ i :=
  toSimplicialObject_map_δ (drop.obj A) i

theorem toSimplicialAugmented_left_σ (A : Augmented C) {n : ℕ}
    (i : Fin (n + 1)) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented A)).σ i =
      (drop.obj A).σ i :=
  toSimplicialObject_map_σ (drop.obj A) i

/--
Functor `Data.Augmented C ⥤ SimplicialObject.Augmented C` transporting augmented data
via `Data.toSimplicialFunctor` and the constant comparison `constFunctorIso`.
-/
noncomputable def toSimplicialFunctor :
    Augmented C ⥤ SimplicialObject.Augmented C :=
  Comma.map (F₁ := Data.toSimplicialFunctor (C := C)) (F₂ := 𝟭 C)
    (F := Data.toSimplicialFunctor (C := C))
    (Iso.refl _).hom (constFunctorIso (C := C)).hom

@[simp]
theorem toSimplicialFunctor_obj_left (A : Augmented C) :
    (toSimplicialFunctor (C := C).obj A).left =
      Data.toSimplicialFunctor.obj (drop.obj A) :=
  rfl

@[simp]
theorem toSimplicialFunctor_obj_right (A : Augmented C) :
    (toSimplicialFunctor (C := C).obj A).right = point.obj A :=
  rfl

@[simp]
theorem toSimplicialFunctor_obj_hom (A : Augmented C) :
    (toSimplicialFunctor (C := C).obj A).hom =
      Data.toSimplicialNatTrans (A.hom : drop.obj A ⟶ constData (point.obj A)) ≫
        (constFunctorIso (C := C)).hom.app (point.obj A) := by
  have h : (toSimplicialFunctor (C := C).obj A).hom =
      (Iso.refl (Data.toSimplicialFunctor (C := C))).hom.app (drop.obj A) ≫
        Data.toSimplicialFunctor.map A.hom ≫
          (constFunctorIso (C := C)).hom.app (point.obj A) := rfl
  rw [h]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

@[simp]
theorem toSimplicialFunctor_map_left {A B : Augmented C} (f : A ⟶ B) :
    (toSimplicialFunctor (C := C).map f).left =
      Data.toSimplicialFunctor.map f.left :=
  rfl

@[simp]
theorem toSimplicialFunctor_map_right {A B : Augmented C} (f : A ⟶ B) :
    (toSimplicialFunctor (C := C).map f).right = f.right :=
  rfl

end Augmented

end Data

end SimplicialObject

end CategoryTheory

end
