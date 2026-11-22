/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# Extensionality for lawful Day convolution realizations

The unit and convolution Kan extensions detect full morphisms in any lawful
Day realization. Equality of the corresponding coefficients gives equality
of morphisms through its faithful interpreting functor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped ExternalProduct

namespace CategoryTheory.LawfulDayConvolutionMonoidalCategoryStruct

universe u₁ u₂ u₃ v₁ v₂ v₃

variable (C : Type u₁) (V : Type u₂) (D : Type u₃)
  [Category.{v₁} C] [Category.{v₂} V] [Category.{v₃} D]
  [MonoidalCategory C] [MonoidalCategory V] [MonoidalCategory D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]

/-- The full actual unit Kan extension detects morphisms in any lawful Day realization. -/
theorem unit_hom_ext {X : D} {f g : 𝟙_ D ⟶ X}
    (h : LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V D ≫
      ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).map f).app (𝟙_ C) =
    LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V D ≫
      ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).map g).app (𝟙_ C)) : f = g := by
  let α : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙
      (LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).obj (𝟙_ D) :=
    { app _ := LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V D }
  let : ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).obj (𝟙_ D)).IsLeftKanExtension α :=
    (LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit C V D).isLeftKanExtension
  apply (LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).map_injective
  apply Functor.hom_ext_of_isLeftKanExtension _ α
  apply NatTrans.ext
  funext q
  exact h

/-- The complete actual tensor Kan extension detects morphisms in any lawful Day realization. -/
theorem tensor_hom_ext {X Y Z : D} {f g : X ⊗ Y ⟶ Z}
    (h : ∀ a b : C,
      (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit C V X Y).app (a, b) ≫
        ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).map f).app (a ⊗ b) =
      (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit C V X Y).app (a, b) ≫
        ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).map g).app (a ⊗ b)) : f = g := by
  let : ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).obj (X ⊗ Y)).IsLeftKanExtension
      (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit C V X Y) :=
    (LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      X Y).isLeftKanExtension
  apply (LawfulDayConvolutionMonoidalCategoryStruct.ι C V D).map_injective
  apply Functor.hom_ext_of_isLeftKanExtension _
    (LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit C V X Y)
  apply NatTrans.ext
  funext q
  exact h q.1 q.2

end CategoryTheory.LawfulDayConvolutionMonoidalCategoryStruct
