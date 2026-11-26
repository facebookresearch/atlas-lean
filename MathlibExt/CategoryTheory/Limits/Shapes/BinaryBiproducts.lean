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
# Composition formulas for binary biproducts

In a category with zero morphisms, each chosen binary biproduct has universal maps desc(f,g)
out of its two factors and lift(g,h) into them. Postcomposition distributes over desc, and
precomposition distributes over lift.

For two binary biproducts, a morphism with four entries fᵢⱼ can be constructed either by
taking a desc of two lifts or a lift of two descs. The two expressions agree by their
injection and projection equations. Each statement requires only its specified binary
biproducts; no preadditive structure is assumed.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Postcomposition of a binary biproduct descendant.

In a category with zero morphisms and a chosen biproduct X ⊞ Y, maps f : X → Z, g : Y → Z and
h : Z → W satisfy desc(f,g) ≫ h = desc(f ≫ h,g ≫ h). Both sides restrict to the same
composites on the two injections. -/
@[simp, reassoc]
lemma biprod.desc_comp {X Y Z W : C} [HasBinaryBiproduct X Y]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  apply biprod.hom_ext' _ _
  all_goals simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc,
    biprod.inl_desc, biprod.inr_desc]

/-- Precomposition of a binary biproduct lift.

In a category with zero morphisms and a chosen biproduct Z ⊞ W, maps f : X → Y, g : Y → Z and
h : Y → W satisfy f ≫ lift(g,h) = lift(f ≫ g,f ≫ h). Both sides have the same composites with
the two projections. -/
@[simp, reassoc]
lemma biprod.comp_lift {X Y Z W : C} [HasBinaryBiproduct Z W]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Y ⟶ W) :
    f ≫ biprod.lift g h = biprod.lift (f ≫ g) (f ≫ h) := by
  apply biprod.hom_ext _ _
  all_goals simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]

/-- Equivalent constructions of a biproduct matrix map.

For chosen biproducts X₁ ⊞ X₂ and Y₁ ⊞ Y₂ in a category with zero morphisms, let fᵢⱼ : Xᵢ → Yⱼ
be four maps. The map desc(lift(f₁₁,f₁₂),lift(f₂₁,f₂₂)) equals
lift(desc(f₁₁,f₂₁),desc(f₁₂,f₂₂)); both have the same four injection-to-projection entries. -/
lemma biprod.desc_lift_lift {X₁ X₂ Y₁ Y₂ : C}
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂]
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    biprod.desc (biprod.lift f₁₁ f₁₂) (biprod.lift f₂₁ f₂₂) =
      biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂) := by
  apply biprod.hom_ext' _ _
  all_goals simp only [biprod.comp_lift, biprod.inl_desc, biprod.inr_desc]

end CategoryTheory.Limits
