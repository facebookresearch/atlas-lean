/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorHom

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe uV vV

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.MappingCompositionAlgebra

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]

omit [BraidedCategory V] in
/-- Full internal-Hom composition is natural in its original middle-object arrow. -/
theorem middle_whisker (X Y Z W : V) (f : Y ⟶ Z) :
    eHomWhiskerLeft V X f ▷ ((ihom Z).obj W) ≫ eComp V X Z W =
      ((ihom X).obj Y) ◁ eHomWhiskerRight V f W ≫ eComp V X Y W := by
  let H : V := (ihom X).obj Y
  let L : V := (ihom Y).obj Z
  let K : V := (ihom Z).obj W
  let p : 𝟙_ V ⟶ L := eHomEquiv V f
  let x : H ⊗ L ⟶ (ihom X).obj Z := eComp V X Y Z
  let y : ((ihom X).obj Z) ⊗ K ⟶ (ihom X).obj W := eComp V X Z W
  let z : L ⊗ K ⟶ (ihom Y).obj W := eComp V Y Z W
  let w : H ⊗ ((ihom Y).obj W) ⟶ (ihom X).obj W := eComp V X Y W
  have hAssoc : (x ▷ K) ≫ y = (α_ H L K).hom ≫ (H ◁ z) ≫ w :=
    (e_assoc' V X Y Z W).symm
  have hNat : ((H ◁ p) ▷ K) ≫ (α_ H L K).hom =
      (α_ H (𝟙_ V) K).hom ≫ (H ◁ (p ▷ K)) := associator_naturality_middle H p K
  have hTriangle : ((ρ_ H).inv ▷ K) ≫ (α_ H (𝟙_ V) K).hom =
      H ◁ (λ_ K).inv := triangle_assoc_comp_right_inv H K
  simp only [eHomWhiskerLeft, eHomWhiskerRight, comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  change ((ρ_ H).inv ▷ K) ≫ ((H ◁ p) ▷ K) ≫ (x ▷ K) ≫ y =
    (H ◁ (λ_ K).inv) ≫ (H ◁ (p ▷ K)) ≫ (H ◁ z) ≫ w
  calc
    _ = ((ρ_ H).inv ▷ K) ≫ ((H ◁ p) ▷ K) ≫ (α_ H L K).hom ≫ (H ◁ z) ≫ w := by
      rw [hAssoc]
    _ = ((ρ_ H).inv ▷ K) ≫
        (((H ◁ p) ▷ K) ≫ (α_ H L K).hom) ≫ (H ◁ z) ≫ w := by
      simp only [Category.assoc]
    _ = ((ρ_ H).inv ▷ K) ≫
        ((α_ H (𝟙_ V) K).hom ≫ (H ◁ (p ▷ K))) ≫ (H ◁ z) ≫ w := by rw [hNat]
    _ = (((ρ_ H).inv ▷ K) ≫ (α_ H (𝟙_ V) K).hom) ≫
        (H ◁ (p ▷ K)) ≫ (H ◁ z) ≫ w := by simp only [Category.assoc]
    _ = _ := by rw [hTriangle]

omit [BraidedCategory V] in
/-- Complete parameter Hom composition is natural under target postcomposition. -/
theorem parameter_post {P Q : V} (X Y Z Z' : V) (r : Z ⟶ Z')
    (f : P ⟶ (ihom X).obj Y) (g : Q ⟶ (ihom Y).obj Z) :
    (f ⊗ₘ g) ≫ eComp V X Y Z ≫ eHomWhiskerLeft V X r =
      (f ⊗ₘ (g ≫ eHomWhiskerLeft V Y r)) ≫ eComp V X Y Z' := by
  rw [eComp_eHomWhiskerLeft]
  rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  change (((f ≫ 𝟙 ((ihom X).obj Y)) ⊗ₘ (g ≫ eHomWhiskerLeft V Y r)) ≫
      eComp V X Y Z') = _
  rw [Category.comp_id]

omit [BraidedCategory V] in
/-- Complete parameter Hom composition is natural under source precomposition. -/
theorem parameter_pre {P Q : V} (X' X Y Z : V) (r : X' ⟶ X)
    (f : P ⟶ (ihom X).obj Y) (g : Q ⟶ (ihom Y).obj Z) :
    ((f ≫ eHomWhiskerRight V r Y) ⊗ₘ g) ≫ eComp V X' Y Z =
      (f ⊗ₘ g) ≫ eComp V X Y Z ≫ eHomWhiskerRight V r Z := by
  symm
  rw [eComp_eHomWhiskerRight]
  rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc]
  change (((f ≫ eHomWhiskerRight V r Y) ⊗ₘ (g ≫ 𝟙 ((ihom Y).obj Z))) ≫
      eComp V X' Y Z) = _
  rw [Category.comp_id]

omit [BraidedCategory V] in
/-- The entire original middle-object action is moved between both complete Hom factors. -/
theorem parameter_middle {P Q : V} (X Y Z W : V) (r : Y ⟶ Z)
    (f : P ⟶ (ihom X).obj Y) (g : Q ⟶ (ihom Z).obj W) :
    (f ⊗ₘ (g ≫ eHomWhiskerRight V r W)) ≫ eComp V X Y W =
      ((f ≫ eHomWhiskerLeft V X r) ⊗ₘ g) ≫ eComp V X Z W := by
  calc
    _ = (f ⊗ₘ g) ≫ ((ihom X).obj Y ◁ eHomWhiskerRight V r W) ≫ eComp V X Y W := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
    _ = (f ⊗ₘ g) ≫ (eHomWhiskerLeft V X r ▷ (ihom Z).obj W) ≫ eComp V X Z W :=
      congrArg (fun z => (f ⊗ₘ g) ≫ z) (middle_whisker X Y Z W r).symm
    _ = _ := by
      rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]

omit [BraidedCategory V] in
/-- Every complete original index relation is preserved by actual parameter composition. -/
theorem compose_index {P Q : V} (X X' Y Y' Z Z' : V)
    (rX : X ⟶ X') (rY : Y ⟶ Y') (rZ : Z ⟶ Z')
    (f : P ⟶ (ihom X).obj Y) (f' : P ⟶ (ihom X').obj Y')
    (g : Q ⟶ (ihom Y).obj Z) (g' : Q ⟶ (ihom Y').obj Z')
    (hf : f ≫ eHomWhiskerLeft V X rY = f' ≫ eHomWhiskerRight V rX Y')
    (hg : g ≫ eHomWhiskerLeft V Y rZ = g' ≫ eHomWhiskerRight V rY Z') :
    (f ⊗ₘ g) ≫ eComp V X Y Z ≫ eHomWhiskerLeft V X rZ =
      (f' ⊗ₘ g') ≫ eComp V X' Y' Z' ≫ eHomWhiskerRight V rX Z' := by
  rw [parameter_post, hg, parameter_middle, hf, parameter_pre]

/-- Every complete original coefficient-right relation is preserved by actual composition. -/
theorem compose_right_action {P Q : V} (X X' Y Y' Z Z' A : V)
    (rX : X ⊗ A ⟶ X') (rY : Y ⊗ A ⟶ Y') (rZ : Z ⊗ A ⟶ Z')
    (f : P ⟶ (ihom X).obj Y) (f' : P ⟶ (ihom X').obj Y')
    (g : Q ⟶ (ihom Y).obj Z) (g' : Q ⟶ (ihom Y').obj Z')
    (hf : f' ≫ eHomWhiskerRight V rX Y' =
      f ≫ (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Y ≫
        eHomWhiskerLeft V (X ⊗ A) rY)
    (hg : g' ≫ eHomWhiskerRight V rY Z' =
      g ≫ (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map Y Z ≫
        eHomWhiskerLeft V (Y ⊗ A) rZ) :
    (f' ⊗ₘ g') ≫ eComp V X' Y' Z' ≫ eHomWhiskerRight V rX Z' =
      (f ⊗ₘ g) ≫ eComp V X Y Z ≫ (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Z ≫
        eHomWhiskerLeft V (X ⊗ A) rZ := by
  have hf' := (Category.assoc f ((SphereOperator.fixedRightTensor
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Y)
    (eHomWhiskerLeft V (X ⊗ A) rY)).trans hf.symm
  have hg' := (Category.assoc g ((SphereOperator.fixedRightTensor
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map Y Z)
    (eHomWhiskerLeft V (Y ⊗ A) rZ)).trans hg.symm
  have h := compose_index (X ⊗ A) X' (Y ⊗ A) Y' (Z ⊗ A) Z' rX rY rZ
    (f ≫ (SphereOperator.fixedRightTensor
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Y) f'
    (g ≫ (SphereOperator.fixedRightTensor
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map Y Z) g' hf' hg'
  symm at h
  have ht :
      ((f ≫ (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Y) ⊗ₘ
        (g ≫ (SphereOperator.fixedRightTensor
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map Y Z)) ≫
          eComp V (X ⊗ A) (Y ⊗ A) (Z ⊗ A) =
      (f ⊗ₘ g) ≫ eComp V X Y Z ≫ (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Z := by
    let tx : (ihom X).obj Y ⟶ (ihom (X ⊗ A)).obj (Y ⊗ A) :=
      (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Y
    let ty : (ihom Y).obj Z ⟶ (ihom (Y ⊗ A)).obj (Z ⊗ A) :=
      (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map Y Z
    have hcomp := SphereOperator.fixedRightTensor_comp
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A X Y Z
    simp only [SphereOperator.fixedRightTensor_obj] at hcomp
    have hTensor := tensorHom_comp_tensorHom f g tx ty
    exact (congrArg (fun z => z ≫ eComp V (X ⊗ A) (Y ⊗ A) (Z ⊗ A)) hTensor.symm).trans
      ((Category.assoc (f ⊗ₘ g) (tx ⊗ₘ ty) _).trans
        (congrArg (fun z => (f ⊗ₘ g) ≫ z) hcomp.symm))
  let p := (f ≫ (SphereOperator.fixedRightTensor
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Y) ⊗ₘ
    (g ≫ (SphereOperator.fixedRightTensor
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map Y Z)
  let q := f ⊗ₘ g
  let c := eComp V X Y Z
  let ca := eComp V (X ⊗ A) (Y ⊗ A) (Z ⊗ A)
  let t := (SphereOperator.fixedRightTensor
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) A).map X Z
  let r := eHomWhiskerLeft V (X ⊗ A) rZ
  have hc : p ≫ ca ≫ r = q ≫ c ≫ t ≫ r :=
    (Category.assoc p ca r).symm.trans
      ((congrArg (fun z => z ≫ r) ht).trans
        ((Category.assoc q (c ≫ t) r).trans
          (congrArg (fun z => q ≫ z) (Category.assoc c t r))))
  exact h.trans hc

end CategoryTheory.Enriched.MappingCompositionAlgebra
