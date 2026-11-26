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
# Coordinates of binary and nested biproduct matrix maps

Let C be preadditive with binary biproducts. For maps fᵢⱼ : X_i → Y_j, the binary matrix map
X₁ ⊞ X₂ → Y₁ ⊞ Y₂ is desc(lift(f₁₁,f₁₂),lift(f₂₁,f₂₂)). Postcomposing with desc(g₁,g₂) gives
desc(f₁₁ ≫ g₁ + f₁₂ ≫ g₂, f₂₁ ≫ g₁ + f₂₂ ≫ g₂).

For three factors, the nested matrix retains the order (X₁ ⊞ X₂) ⊞ X₃ and (Y₁ ⊞ Y₂) ⊞ Y₃. Its
row maps are lift(lift(fᵢ₁,fᵢ₂),fᵢ₃), assembled by desc(desc(row₁,row₂),row₃). The object and
morphism universes remain independent.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Binary matrix map as a descendant of row lifts.

In a preadditive category with binary biproducts, the map with entries fᵢⱼ : X_i → Y_j is
Biprod.ofComponents(f₁₁,f₁₂,f₂₁,f₂₂) = desc(lift(f₁₁,f₁₂),lift(f₂₁,f₂₂)). Its source is X₁ ⊞
X₂ and target Y₁ ⊞ Y₂. -/
lemma Biprod.ofComponents_eq_desc_lift {X₁ X₂ Y₁ Y₂ : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ =
      biprod.desc (biprod.lift f₁₁ f₁₂) (biprod.lift f₂₁ f₂₂) := by
  simp only [Biprod.ofComponents, biprod.desc_eq, biprod.lift_eq,
    Preadditive.comp_add, add_assoc]

/-- Composition of a binary matrix with an output descendant.

For entries fᵢⱼ : X_i → Y_j and maps g_j : Y_j → Z in a preadditive category with binary
biproducts, the matrix followed by desc(g₁,g₂) equals desc(f₁₁ ≫ g₁ + f₁₂ ≫ g₂, f₂₁ ≫ g₁ + f₂₂
≫ g₂). -/
@[reassoc]
lemma Biprod.ofComponents_desc {X₁ X₂ Y₁ Y₂ Z : C}
    (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z) :
    Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.desc g₁ g₂ =
      biprod.desc (f₁₁ ≫ g₁ + f₁₂ ≫ g₂) (f₂₁ ≫ g₁ + f₂₂ ≫ g₂) := by
  rw [Biprod.ofComponents_eq_desc_lift, biprod.desc_comp,
    biprod.lift_desc, biprod.lift_desc]

/-- Three-factor matrix in nested biproduct coordinates.

For entries fᵢⱼ : X_i → Y_j in a preadditive category with binary biproducts, the nested block
matrix from (X₁ ⊞ X₂) ⊞ X₃ to (Y₁ ⊞ Y₂) ⊞ Y₃ equals desc(desc(row₁,row₂),row₃), where row_i =
lift(lift(fᵢ₁,fᵢ₂),fᵢ₃). The formula retains the displayed nesting and factor order. -/
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
