/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Interval actions under monoidal functors and tensor products

A strong monoidal functor transports an actual interval action through its
forward tensor constraint. Tensoring that action with an arbitrary object uses
the inverse associator. The full endpoint and fixed-subspace equations follow
from tensor naturality and unit coherence; no assumption is made on the extra
object beyond membership in the monoidal category.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v uC vC uD vD

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor.CoreMonoidal

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  (F : C ⥤ D) (hF : F.CoreMonoidal)

/-- Map the complete interval action using the forward selected tensor constraint. -/
def intervalActionImage {I Y : C} (H : I ⊗ Y ⟶ Y) :
    F.obj I ⊗ F.obj Y ⟶ F.obj Y :=
  (hF.μIso I Y).hom ≫ F.map H

/-- The image of an interval collapse uses the inverse selected unit constraint. -/
def intervalCollapseImage {I : C} (c : I ⟶ 𝟙_ C) :
    F.obj I ⟶ 𝟙_ D :=
  F.map c ≫ hF.εIso.inv

/-- The complete fixed-subspace equation transports along the actual tensor
and unit constraints, with no assumed equation on the transported action. -/
theorem intervalActionImage_fix {I X Y : C} (H : I ⊗ Y ⟶ Y)
    (i : X ⟶ Y) (c : I ⟶ 𝟙_ C)
    (hfix : (𝟙 I ⊗ₘ i) ≫ H =
      (c ⊗ₘ 𝟙 X) ≫ (λ_ X).hom ≫ i) :
    (𝟙 (F.obj I) ⊗ₘ F.map i) ≫ intervalActionImage F hF H =
      (intervalCollapseImage F hF c ⊗ₘ 𝟙 (F.obj X)) ≫
        (λ_ (F.obj X)).hom ≫ F.map i := by
  have hUnit : (hF.μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom =
      hF.εIso.inv ▷ F.obj X ≫ (λ_ (F.obj X)).hom := by
    have h := congrArg
      (fun g : 𝟙_ D ⊗ F.obj X ⟶ F.obj X =>
        hF.εIso.inv ▷ F.obj X ≫ g)
      (hF.left_unitality X)
    simpa only [Category.assoc, inv_hom_whiskerRight_assoc] using h.symm
  have hRight :
      (𝟙 (F.obj I) ⊗ₘ F.map i) ≫ (hF.μIso I Y).hom ≫ F.map H =
        (hF.μIso I X).hom ≫ F.map (𝟙 I ⊗ₘ i) ≫ F.map H := by
    simpa only [id_tensorHom, Category.assoc] using congrArg
      (fun g : F.obj I ⊗ F.obj X ⟶ F.obj (I ⊗ Y) => g ≫ F.map H)
      (hF.μIso_hom_natural_right I i)
  have hLeft : (hF.μIso I X).hom ≫ F.map (c ⊗ₘ 𝟙 X) =
      (F.map c ⊗ₘ 𝟙 (F.obj X)) ≫ (hF.μIso (𝟙_ C) X).hom := by
    simpa only [tensorHom_id] using (hF.μIso_hom_natural_left c X).symm
  calc
    _ = (hF.μIso I X).hom ≫ F.map (𝟙 I ⊗ₘ i) ≫ F.map H := by
      simpa only [intervalActionImage, Category.assoc] using hRight
    _ = (hF.μIso I X).hom ≫
        F.map ((c ⊗ₘ 𝟙 X) ≫ (λ_ X).hom ≫ i) := by
      rw [← F.map_comp, hfix]
    _ = (F.map c ⊗ₘ 𝟙 (F.obj X)) ≫
        (hF.μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom ≫ F.map i := by
      rw [F.map_comp, F.map_comp]
      simpa only [Category.assoc] using congrArg
        (fun g : F.obj I ⊗ F.obj X ⟶ F.obj (𝟙_ C ⊗ X) =>
          g ≫ F.map (λ_ X).hom ≫ F.map i) hLeft
    _ = (F.map c ⊗ₘ 𝟙 (F.obj X)) ≫
        hF.εIso.inv ▷ F.obj X ≫ (λ_ (F.obj X)).hom ≫ F.map i := by
      simpa only [Category.assoc] using congrArg
        (fun g : F.obj (𝟙_ C) ⊗ F.obj X ⟶ F.obj X =>
          (F.map c ⊗ₘ 𝟙 (F.obj X)) ≫ g ≫ F.map i) hUnit
    _ = _ := by
      simp only [intervalCollapseImage, tensorHom_id,
        comp_whiskerRight, Category.assoc]

/-- The image of an actual endpoint satisfies the full source endpoint
endomorphism equation, using the original unit and tensor naturality laws. -/
theorem intervalActionImage_endpoint {I Y : C} (H : I ⊗ Y ⟶ Y)
    (e : 𝟙_ C ⟶ I) (f : Y ⟶ Y)
    (hEndpoint : (λ_ Y).inv ≫ (e ⊗ₘ 𝟙 Y) ≫ H = f) :
    (λ_ (F.obj Y)).inv ≫
        ((hF.εIso.hom ≫ F.map e) ⊗ₘ 𝟙 (F.obj Y)) ≫
        intervalActionImage F hF H = F.map f := by
  have hUnit : (λ_ (F.obj Y)).inv ≫ hF.εIso.hom ▷ F.obj Y ≫
      (hF.μIso (𝟙_ C) Y).hom = F.map (λ_ Y).inv := by
    apply (cancel_mono (F.map (λ_ Y).hom)).1
    calc
      ((λ_ (F.obj Y)).inv ≫ hF.εIso.hom ▷ F.obj Y ≫
          (hF.μIso (𝟙_ C) Y).hom) ≫ F.map (λ_ Y).hom =
          (λ_ (F.obj Y)).inv ≫ (λ_ (F.obj Y)).hom := by
        simpa only [Category.assoc] using congrArg
          (fun g => (λ_ (F.obj Y)).inv ≫ g) (hF.left_unitality Y).symm
      _ = F.map (λ_ Y).inv ≫ F.map (λ_ Y).hom := by
        simp only [← F.map_comp, Iso.inv_hom_id, F.map_id]
  have hTensor := hF.μIso_hom_natural_left e Y
  have hTensorFull := congrArg
    (fun g => (λ_ (F.obj Y)).inv ≫ hF.εIso.hom ▷ F.obj Y ≫ g ≫ F.map H)
      hTensor
  calc
    _ = (λ_ (F.obj Y)).inv ≫ hF.εIso.hom ▷ F.obj Y ≫
        (hF.μIso (𝟙_ C) Y).hom ≫ F.map (e ▷ Y) ≫ F.map H := by
      simpa only [intervalActionImage, tensorHom_id,
        comp_whiskerRight, Category.assoc] using hTensorFull
    _ = F.map (λ_ Y).inv ≫ F.map (e ▷ Y) ≫ F.map H := by
      simpa only [Category.assoc] using congrArg
        (fun g => g ≫ F.map (e ▷ Y) ≫ F.map H) hUnit
    _ = F.map ((λ_ Y).inv ≫ (e ⊗ₘ 𝟙 Y) ≫ H) := by
      rw [tensorHom_id, F.map_comp, F.map_comp]
    _ = F.map f := congrArg F.map hEndpoint

end CategoryTheory.Functor.CoreMonoidal

namespace CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
/-- Tensor an actual interval action map with an arbitrary object using the selected associator. -/
def tensorIntervalMap {I Y : C} (H : I ⊗ Y ⟶ Y) (K : C) :
    I ⊗ (Y ⊗ K) ⟶ Y ⊗ K :=
  (α_ I Y K).inv ≫ (H ⊗ₘ 𝟙 K)
/-- Its complete endpoint map is the tensor of the original endpoint composite. -/
theorem tensorIntervalMap_endpoint {I Y : C} (H : I ⊗ Y ⟶ Y)
    (e : 𝟙_ C ⟶ I) (K : C) :
    (λ_ (Y ⊗ K)).inv ≫ (e ⊗ₘ 𝟙 (Y ⊗ K)) ≫ tensorIntervalMap H K =
      ((λ_ Y).inv ≫ (e ⊗ₘ 𝟙 Y) ≫ H) ⊗ₘ 𝟙 K := by
  dsimp only [tensorIntervalMap]
  rw [MonoidalCategory.tensorHom_id]
  rw [MonoidalCategory.associator_inv_naturality_left_assoc]
  rw [MonoidalCategory.leftUnitor_tensor_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.comp_whiskerRight]
/-- The complete tensor interval map fixes the original included subobject whenever H does. -/
theorem tensorIntervalMap_fix {I X Y : C} (H : I ⊗ Y ⟶ Y)
    (i : X ⟶ Y) (c : I ⟶ 𝟙_ C)
    (hfix : (𝟙 I ⊗ₘ i) ≫ H = (c ⊗ₘ 𝟙 X) ≫ (λ_ X).hom ≫ i)
    (K : C) :
    (𝟙 I ⊗ₘ (i ⊗ₘ 𝟙 K)) ≫ tensorIntervalMap H K =
      (c ⊗ₘ 𝟙 (X ⊗ K)) ≫ (λ_ (X ⊗ K)).hom ≫ (i ⊗ₘ 𝟙 K) := by
  have hInput :
      (𝟙 I ⊗ₘ (i ⊗ₘ 𝟙 K)) ≫ (α_ I Y K).inv =
        (α_ I X K).inv ≫ ((𝟙 I ⊗ₘ i) ⊗ₘ 𝟙 K) := by
    simpa only [MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_id] using
      (MonoidalCategory.associator_inv_naturality_middle I i K)
  have hCollapse :
      (α_ I X K).inv ≫ ((c ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 K) =
        (c ⊗ₘ 𝟙 (X ⊗ K)) ≫ (α_ (𝟙_ C) X K).inv := by
    simpa only [MonoidalCategory.tensorHom_id] using
      (MonoidalCategory.associator_inv_naturality_left c X K).symm
  have hCollapseWhisker :
      (α_ I X K).inv ≫ c ▷ X ▷ K =
        c ▷ (X ⊗ K) ≫ (α_ (𝟙_ C) X K).inv := by
    simpa only [MonoidalCategory.tensorHom_id] using hCollapse
  calc
    (𝟙 I ⊗ₘ (i ⊗ₘ 𝟙 K)) ≫ tensorIntervalMap H K =
        (α_ I X K).inv ≫ (((𝟙 I ⊗ₘ i) ≫ H) ⊗ₘ 𝟙 K) := by
      dsimp only [tensorIntervalMap]
      rw [← Category.assoc, hInput]
      simp only [Category.assoc]
      rw [tensorHom_comp_tensorHom]
      simp only [Category.id_comp]
    _ = (α_ I X K).inv ≫
        (((c ⊗ₘ 𝟙 X) ≫ (λ_ X).hom ≫ i) ⊗ₘ 𝟙 K) := by
      rw [hfix]
    _ = (c ⊗ₘ 𝟙 (X ⊗ K)) ≫
        (λ_ (X ⊗ K)).hom ≫ (i ⊗ₘ 𝟙 K) := by
      simp only [MonoidalCategory.tensorHom_id,
        MonoidalCategory.comp_whiskerRight]
      slice_lhs 1 2 => rw [hCollapseWhisker]
      rw [MonoidalCategory.leftUnitor_tensor_hom]
      simp only [Category.assoc]
end CategoryTheory.MonoidalCategory
