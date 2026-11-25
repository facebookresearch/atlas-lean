/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Composition in the actual binary biproduct bicone

These universal equations concern the chosen binary biproduct itself.
Only the individual biproducts in each statement are required.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

@[simp, reassoc]
lemma biprod.desc_comp {X Y Z W : C} [HasBinaryBiproduct X Y]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  apply biprod.hom_ext' _ _
  all_goals simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc,
    biprod.inl_desc, biprod.inr_desc]

@[simp, reassoc]
lemma biprod.comp_lift {X Y Z W : C} [HasBinaryBiproduct Z W]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Y ⟶ W) :
    f ≫ biprod.lift g h = biprod.lift (f ≫ g) (f ≫ h) := by
  apply biprod.hom_ext _ _
  all_goals simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]

/-- Interchanging the universal product and coproduct descriptions keeps the actual bicone. -/
lemma biprod.desc_lift_lift {X₁ X₂ Y₁ Y₂ : C}
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂]
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    biprod.desc (biprod.lift f₁₁ f₁₂) (biprod.lift f₂₁ f₂₂) =
      biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂) := by
  apply biprod.hom_ext' _ _
  all_goals simp only [biprod.comp_lift, biprod.inl_desc, biprod.inr_desc]

end CategoryTheory.Limits
