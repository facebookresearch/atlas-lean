/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor

/-!
# Module action laws on complete Day convolution generators

The unit and multiplication equations are the original module equations
transported through the actual Day convolution generator maps. The complete
coefficient, indexed object, associator, and unitor arrows are retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uV vV uD vD

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct

/-- The actual module unit acts on every original complete Day generator. -/
theorem modulePairUnit
    {C₀ : Type uC} [Category.{vC} C₀] [MonoidalCategory C₀]
    {V₀ : Type uV} [Category.{vV} V₀] [MonoidalCategory V₀]
    {D₀ : Type uD} [Category.{vD} D₀] [MonoidalCategory D₀]
    [LawfulDayConvolutionMonoidalCategoryStruct C₀ V₀ D₀]
    (S₀ X₀ : D₀) [MonObj S₀] [ModObj S₀ X₀] (n₀ : C₀) :
    ((unitUnit C₀ V₀ D₀ ≫
        ((ι C₀ V₀ D₀).map (η : 𝟙_ D₀ ⟶ S₀)).app (𝟙_ C₀)) ▷
      ((ι C₀ V₀ D₀).obj X₀).obj n₀) ≫
    (convolutionExtensionUnit C₀ V₀ S₀ X₀).app (𝟙_ C₀, n₀) ≫
    ((ι C₀ V₀ D₀).map (ModObj.smul (M := S₀) (X := X₀))).app ((𝟙_ C₀) ⊗ n₀) =
    (λ_ (((ι C₀ V₀ D₀).obj X₀).obj n₀)).hom ≫
      ((ι C₀ V₀ D₀).obj X₀).map (λ_ n₀).inv := by
  let J : D₀ ⥤ C₀ ⥤ V₀ := ι C₀ V₀ D₀
  let G : C₀ ⥤ V₀ := J.obj X₀
  let A : V₀ := G.obj n₀
  let U : V₀ := (J.obj (𝟙_ D₀)).obj (𝟙_ C₀)
  let ν : (𝟙_ V₀) ⟶ U := unitUnit C₀ V₀ D₀
  let one : 𝟙_ D₀ ⟶ S₀ := η
  let action : S₀ ⊗ X₀ ⟶ X₀ := ModObj.smul (M := S₀) (X := X₀)
  let η₀ : U ⊗ A ⟶ (J.obj (𝟙_ D₀ ⊗ X₀)).obj ((𝟙_ C₀) ⊗ n₀) :=
    (convolutionExtensionUnit C₀ V₀ (𝟙_ D₀) X₀).app (𝟙_ C₀, n₀)
  let ηS : (J.obj S₀).obj (𝟙_ C₀) ⊗ A ⟶
      (J.obj (S₀ ⊗ X₀)).obj ((𝟙_ C₀) ⊗ n₀) :=
    (convolutionExtensionUnit C₀ V₀ S₀ X₀).app (𝟙_ C₀, n₀)
  let u := (J.map (one ▷ X₀)).app ((𝟙_ C₀) ⊗ n₀)
  let a := (J.map action).app ((𝟙_ C₀) ⊗ n₀)
  let l := (J.map (λ_ X₀).hom).app ((𝟙_ C₀) ⊗ n₀)
  have hModule : one ▷ X₀ ≫ action = (λ_ X₀).hom := ModObj.one_smul_self S₀ X₀
  have hApp : u ≫ a = l :=
    (congrArg
      (fun z : J.obj (𝟙_ D₀ ⊗ X₀) ⟶ J.obj X₀ => z.app ((𝟙_ C₀) ⊗ n₀))
      (J.map_comp (one ▷ X₀) action)).symm.trans
      (congrArg
        (fun z : 𝟙_ D₀ ⊗ X₀ ⟶ X₀ => (J.map z).app ((𝟙_ C₀) ⊗ n₀)) hModule)
  have hConvolution : η₀ ≫ u = ((J.map one).app (𝟙_ C₀) ▷ A) ≫ ηS :=
    convolutionExtensionUnit_comp_ι_map_whiskerRight_app C₀ V₀ one X₀ (𝟙_ C₀) n₀
  have hWhisker : (ν ▷ A) ≫ ((J.map one).app (𝟙_ C₀) ▷ A) =
      (ν ≫ (J.map one).app (𝟙_ C₀)) ▷ A :=
    (MonoidalCategory.comp_whiskerRight ν ((J.map one).app (𝟙_ C₀)) A).symm
  have hUnitor : (ν ▷ A) ≫ η₀ ≫ l = (λ_ A).hom ≫ G.map (λ_ n₀).inv :=
    leftUnitor_hom_unit_app V₀ X₀ n₀
  have hLeg : η₀ ≫ u ≫ a = ((J.map one).app (𝟙_ C₀) ▷ A) ≫ ηS ≫ a :=
    (Category.assoc η₀ u a).symm.trans
      ((congrArg
        (fun z : U ⊗ A ⟶ (J.obj (S₀ ⊗ X₀)).obj ((𝟙_ C₀) ⊗ n₀) => z ≫ a)
        hConvolution).trans
        (Category.assoc ((J.map one).app (𝟙_ C₀) ▷ A) ηS a))
  have hLeft : (ν ▷ A) ≫ η₀ ≫ u ≫ a =
      ((ν ≫ (J.map one).app (𝟙_ C₀)) ▷ A) ≫ ηS ≫ a :=
    (congrArg
      (fun z : U ⊗ A ⟶ G.obj ((𝟙_ C₀) ⊗ n₀) => (ν ▷ A) ≫ z) hLeg).trans
      ((Category.assoc (ν ▷ A) ((J.map one).app (𝟙_ C₀) ▷ A) (ηS ≫ a)).symm.trans
        (congrArg
          (fun z : (𝟙_ V₀) ⊗ A ⟶ (J.obj S₀).obj (𝟙_ C₀) ⊗ A => z ≫ ηS ≫ a)
          hWhisker))
  have hRight : (ν ▷ A) ≫ η₀ ≫ u ≫ a = (ν ▷ A) ≫ η₀ ≫ l :=
    congrArg
      (fun z : (J.obj (𝟙_ D₀ ⊗ X₀)).obj ((𝟙_ C₀) ⊗ n₀) ⟶
        G.obj ((𝟙_ C₀) ⊗ n₀) => (ν ▷ A) ≫ η₀ ≫ z) hApp
  change ((ν ≫ (J.map one).app (𝟙_ C₀)) ▷ A) ≫ ηS ≫ a =
    (λ_ A).hom ≫ G.map (λ_ n₀).inv
  exact hLeft.symm.trans (hRight.trans hUnitor)

/-- The actual module multiplication acts on every original complete Day generator. -/
theorem modulePairMul
    {C₀ : Type uC} [Category.{vC} C₀] [MonoidalCategory C₀]
    {V₀ : Type uV} [Category.{vV} V₀] [MonoidalCategory V₀]
    {D₀ : Type uD} [Category.{vD} D₀] [MonoidalCategory D₀]
    [LawfulDayConvolutionMonoidalCategoryStruct C₀ V₀ D₀]
    (S₀ X₀ : D₀) [MonObj S₀] [ModObj S₀ X₀] (b₀ a₀ n₀ : C₀) :
    (((convolutionExtensionUnit C₀ V₀ S₀ S₀).app (b₀, a₀) ≫
        ((ι C₀ V₀ D₀).map (μ : S₀ ⊗ S₀ ⟶ S₀)).app (b₀ ⊗ a₀)) ▷
      ((ι C₀ V₀ D₀).obj X₀).obj n₀) ≫
    (convolutionExtensionUnit C₀ V₀ S₀ X₀).app (b₀ ⊗ a₀, n₀) ≫
    ((ι C₀ V₀ D₀).map (ModObj.smul (M := S₀) (X := X₀))).app ((b₀ ⊗ a₀) ⊗ n₀) =
    (α_ (((ι C₀ V₀ D₀).obj S₀).obj b₀) (((ι C₀ V₀ D₀).obj S₀).obj a₀)
      (((ι C₀ V₀ D₀).obj X₀).obj n₀)).hom ≫
    (((ι C₀ V₀ D₀).obj S₀).obj b₀ ◁
      ((convolutionExtensionUnit C₀ V₀ S₀ X₀).app (a₀, n₀) ≫
        ((ι C₀ V₀ D₀).map (ModObj.smul (M := S₀) (X := X₀))).app (a₀ ⊗ n₀))) ≫
    (convolutionExtensionUnit C₀ V₀ S₀ X₀).app (b₀, a₀ ⊗ n₀) ≫
    ((ι C₀ V₀ D₀).map (ModObj.smul (M := S₀) (X := X₀))).app (b₀ ⊗ (a₀ ⊗ n₀)) ≫
      ((ι C₀ V₀ D₀).obj X₀).map (α_ b₀ a₀ n₀).inv := by
  let J : D₀ ⥤ C₀ ⥤ V₀ := ι C₀ V₀ D₀
  let S : C₀ ⥤ V₀ := J.obj S₀
  let X : C₀ ⥤ V₀ := J.obj X₀
  let A : V₀ := S.obj b₀
  let B : V₀ := S.obj a₀
  let C : V₀ := X.obj n₀
  let T : C₀ := (b₀ ⊗ a₀) ⊗ n₀
  let T' : C₀ := b₀ ⊗ (a₀ ⊗ n₀)
  let mul : S₀ ⊗ S₀ ⟶ S₀ := μ
  let action : S₀ ⊗ X₀ ⟶ X₀ := ModObj.smul (M := S₀) (X := X₀)
  let Y : C₀ ⥤ V₀ := J.obj (S₀ ⊗ X₀)
  let H : C₀ ⥤ V₀ := J.obj (S₀ ⊗ (S₀ ⊗ X₀))
  let p : A ⊗ B ⟶ (J.obj (S₀ ⊗ S₀)).obj (b₀ ⊗ a₀) :=
    (convolutionExtensionUnit C₀ V₀ S₀ S₀).app (b₀, a₀)
  let μ₀ : A ⊗ B ⟶ S.obj (b₀ ⊗ a₀) := p ≫ (J.map mul).app (b₀ ⊗ a₀)
  let iL : (J.obj (S₀ ⊗ S₀)).obj (b₀ ⊗ a₀) ⊗ C ⟶
      (J.obj ((S₀ ⊗ S₀) ⊗ X₀)).obj T :=
    (convolutionExtensionUnit C₀ V₀ (S₀ ⊗ S₀) X₀).app (b₀ ⊗ a₀, n₀)
  let iS : S.obj (b₀ ⊗ a₀) ⊗ C ⟶ Y.obj T :=
    (convolutionExtensionUnit C₀ V₀ S₀ X₀).app (b₀ ⊗ a₀, n₀)
  let i₀ : B ⊗ C ⟶ Y.obj (a₀ ⊗ n₀) :=
    (convolutionExtensionUnit C₀ V₀ S₀ X₀).app (a₀, n₀)
  let iR : A ⊗ Y.obj (a₀ ⊗ n₀) ⟶ H.obj T' :=
    (convolutionExtensionUnit C₀ V₀ S₀ (S₀ ⊗ X₀)).app (b₀, a₀ ⊗ n₀)
  let iR' : A ⊗ X.obj (a₀ ⊗ n₀) ⟶ Y.obj T' :=
    (convolutionExtensionUnit C₀ V₀ S₀ X₀).app (b₀, a₀ ⊗ n₀)
  let uL : (J.obj ((S₀ ⊗ S₀) ⊗ X₀)).obj T ⟶ Y.obj T :=
    (J.map (mul ▷ X₀)).app T
  let αD : (J.obj ((S₀ ⊗ S₀) ⊗ X₀)).obj T ⟶ H.obj T :=
    (J.map (α_ S₀ S₀ X₀).hom).app T
  let uR : H.obj T ⟶ Y.obj T := (J.map (S₀ ◁ action)).app T
  let uR' : H.obj T' ⟶ Y.obj T' := (J.map (S₀ ◁ action)).app T'
  let aT : Y.obj T ⟶ X.obj T := (J.map action).app T
  let aT' : Y.obj T' ⟶ X.obj T' := (J.map action).app T'
  let a₀' : Y.obj (a₀ ⊗ n₀) ⟶ X.obj (a₀ ⊗ n₀) := (J.map action).app (a₀ ⊗ n₀)
  let t : H.obj T' ⟶ H.obj T := H.map (α_ b₀ a₀ n₀).inv
  have hModule : (mul ▷ X₀) ≫ action =
      (α_ S₀ S₀ X₀).hom ≫ (S₀ ◁ action) ≫ action := ModObj.mul_smul_self S₀ X₀
  have hMapL : (J.map ((mul ▷ X₀) ≫ action)).app T = uL ≫ aT :=
    congrArg
      (fun z : J.obj ((S₀ ⊗ S₀) ⊗ X₀) ⟶ J.obj X₀ => z.app T)
      (J.map_comp (mul ▷ X₀) action)
  have hMapR₀ : (J.map ((S₀ ◁ action) ≫ action)).app T = uR ≫ aT :=
    congrArg
      (fun z : J.obj (S₀ ⊗ (S₀ ⊗ X₀)) ⟶ J.obj X₀ => z.app T)
      (J.map_comp (S₀ ◁ action) action)
  have hMapR :
      (J.map ((α_ S₀ S₀ X₀).hom ≫ (S₀ ◁ action) ≫ action)).app T = αD ≫ uR ≫ aT :=
    (congrArg
      (fun z : J.obj ((S₀ ⊗ S₀) ⊗ X₀) ⟶ J.obj X₀ => z.app T)
      (J.map_comp (α_ S₀ S₀ X₀).hom ((S₀ ◁ action) ≫ action))).trans
      (congrArg (fun z : H.obj T ⟶ X.obj T => αD ≫ z) hMapR₀)
  have hApp : uL ≫ aT = αD ≫ uR ≫ aT :=
    hMapL.symm.trans
      ((congrArg
        (fun z : (S₀ ⊗ S₀) ⊗ X₀ ⟶ X₀ => (J.map z).app T) hModule).trans hMapR)
  have hOuterL : iL ≫ uL = ((J.map mul).app (b₀ ⊗ a₀) ▷ C) ≫ iS :=
    convolutionExtensionUnit_comp_ι_map_whiskerRight_app C₀ V₀ mul X₀ (b₀ ⊗ a₀) n₀
  have hAssoc : (p ▷ C) ≫ iL ≫ αD = (α_ A B C).hom ≫ (A ◁ i₀) ≫ iR ≫ t :=
    associator_hom_unit_unit V₀ S₀ S₀ X₀ b₀ a₀ n₀
  have hNat₁ : t ≫ uR = uR' ≫ Y.map (α_ b₀ a₀ n₀).inv :=
    (J.map (S₀ ◁ action)).naturality (α_ b₀ a₀ n₀).inv
  have hNat₂ : Y.map (α_ b₀ a₀ n₀).inv ≫ aT = aT' ≫ X.map (α_ b₀ a₀ n₀).inv :=
    (J.map action).naturality (α_ b₀ a₀ n₀).inv
  have hNat : t ≫ uR ≫ aT = uR' ≫ aT' ≫ X.map (α_ b₀ a₀ n₀).inv :=
    (Category.assoc t uR aT).symm.trans
      ((congrArg (fun z : H.obj T' ⟶ Y.obj T => z ≫ aT) hNat₁).trans
        ((Category.assoc uR' (Y.map (α_ b₀ a₀ n₀).inv) aT).trans
          (congrArg (fun z : Y.obj T' ⟶ X.obj T => uR' ≫ z) hNat₂)))
  have hOuterR : iR ≫ uR' = (A ◁ a₀') ≫ iR' :=
    convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V₀ S₀ action b₀ (a₀ ⊗ n₀)
  change (μ₀ ▷ C) ≫ iS ≫ aT =
    (α_ A B C).hom ≫ (A ◁ (i₀ ≫ a₀')) ≫ iR' ≫ aT' ≫ X.map (α_ b₀ a₀ n₀).inv
  calc
    _ = ((p ≫ (J.map mul).app (b₀ ⊗ a₀)) ▷ C) ≫ iS ≫ aT := rfl
    _ = (p ▷ C) ≫ ((J.map mul).app (b₀ ⊗ a₀) ▷ C) ≫ iS ≫ aT := by
      simpa only [Category.assoc] using congrArg
        (fun z : (A ⊗ B) ⊗ C ⟶ S.obj (b₀ ⊗ a₀) ⊗ C => z ≫ iS ≫ aT)
        (MonoidalCategory.comp_whiskerRight p ((J.map mul).app (b₀ ⊗ a₀)) C)
    _ = (p ▷ C) ≫ iL ≫ uL ≫ aT := by
      simpa only [Category.assoc] using congrArg
        (fun z : (J.obj (S₀ ⊗ S₀)).obj (b₀ ⊗ a₀) ⊗ C ⟶ Y.obj T =>
          (p ▷ C) ≫ z ≫ aT) hOuterL.symm
    _ = (p ▷ C) ≫ iL ≫ αD ≫ uR ≫ aT :=
      congrArg
        (fun z : (J.obj ((S₀ ⊗ S₀) ⊗ X₀)).obj T ⟶ X.obj T =>
          (p ▷ C) ≫ iL ≫ z) hApp
    _ = (α_ A B C).hom ≫ (A ◁ i₀) ≫ iR ≫ t ≫ uR ≫ aT := by
      simpa only [Category.assoc] using congrArg
        (fun z : (A ⊗ B) ⊗ C ⟶ H.obj T => z ≫ uR ≫ aT) hAssoc
    _ = (α_ A B C).hom ≫ (A ◁ i₀) ≫ iR ≫ uR' ≫ aT' ≫
        X.map (α_ b₀ a₀ n₀).inv :=
      congrArg (fun z : H.obj T' ⟶ X.obj T => (α_ A B C).hom ≫ (A ◁ i₀) ≫ iR ≫ z)
        hNat
    _ = (α_ A B C).hom ≫ (A ◁ i₀) ≫ (A ◁ a₀') ≫ iR' ≫ aT' ≫
        X.map (α_ b₀ a₀ n₀).inv := by
      simpa only [Category.assoc] using congrArg
        (fun z : A ⊗ Y.obj (a₀ ⊗ n₀) ⟶ Y.obj T' =>
          (α_ A B C).hom ≫ (A ◁ i₀) ≫ z ≫ aT' ≫ X.map (α_ b₀ a₀ n₀).inv) hOuterR
    _ = _ := by simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

end CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct
