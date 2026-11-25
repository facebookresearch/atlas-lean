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

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import MathlibExt.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Literal coordinates for native binary biproduct matrices

The matrix object and multiplication remain native `Biprod.ofComponents`
and `Biprod.ofComponents_comp`. These equations recover the literal
desc/lift and nested three-entry coordinates of actual consumers.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The native matrix has the actual universal desc/lift coordinates. -/
lemma Biprod.ofComponents_eq_desc_lift {X₁ X₂ Y₁ Y₂ : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ =
      biprod.desc (biprod.lift f₁₁ f₁₂) (biprod.lift f₂₁ f₂₂) := by
  simp only [Biprod.ofComponents, biprod.desc_eq, biprod.lift_eq,
    Preadditive.comp_add, add_assoc]

/-- Binary matrix-vector composition on the actual chosen biproduct. -/
@[reassoc]
lemma Biprod.ofComponents_desc {X₁ X₂ Y₁ Y₂ Z : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z) :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.desc g₁ g₂ =
      biprod.desc (f₁₁ ≫ g₁ + f₁₂ ≫ g₂) (f₂₁ ≫ g₁ + f₂₂ ≫ g₂) := by
  rw [Biprod.ofComponents_eq_desc_lift, biprod.desc_comp,
    biprod.lift_desc, biprod.lift_desc]

/-- The existing native block matrix retains the literal `(X₁ ⊞ X₂) ⊞ X₃` order. -/
lemma Biprod.ofComponents_nested_eq_desc_lift {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₁₃ : X₁ ⟶ Y₃)
    (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) (f₂₃ : X₂ ⟶ Y₃)
    (f₃₁ : X₃ ⟶ Y₁) (f₃₂ : X₃ ⟶ Y₂) (f₃₃ : X₃ ⟶ Y₃) :
    Biprod.ofComponents (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂)
        (biprod.desc f₁₃ f₂₃) (biprod.lift f₃₁ f₃₂) f₃₃ =
      biprod.desc
        (biprod.desc (biprod.lift (biprod.lift f₁₁ f₁₂) f₁₃)
          (biprod.lift (biprod.lift f₂₁ f₂₂) f₂₃))
        (biprod.lift (biprod.lift f₃₁ f₃₂) f₃₃) := by
  rw [Biprod.ofComponents_eq_desc_lift
      (Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂) (biprod.desc f₁₃ f₂₃)
      (biprod.lift f₃₁ f₃₂) f₃₃,
    Biprod.ofComponents_eq_desc_lift f₁₁ f₁₂ f₂₁ f₂₂,
    ← biprod.desc_lift_lift]

end CategoryTheory
