/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Equality of entire given functorial factorization data

The middle functor and its two natural transformations determine the entire given record.
The original class proofs and factorization proof remain proof irrelevant. Reclassification
uses `ofLE` on the same given maps and chooses no new factorization.
-/

@[expose] public section

set_option autoImplicit false
universe u v

open CategoryTheory

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type u} [Category.{v} C] {W₁ W₂ V₁ V₂ : MorphismProperty C}

/-- Equal given middle functors and both entire natural maps give equal full records. -/
theorem eq_of_middle_and_heq_natural_maps
    (first second : FunctorialFactorizationData W₁ W₂)
    (middle : first.Z = second.Z) (inclusion : HEq first.i second.i)
    (projection : HEq first.p second.p) : first = second := by
  cases first
  cases second
  cases middle
  cases inclusion
  cases projection
  rfl

/-- Reclassifying the same given data preserves its entire middle functor. -/
theorem ofLE_middle_exact (data : FunctorialFactorizationData W₁ W₂)
    (firstClass : W₁ ≤ V₁) (secondClass : W₂ ≤ V₂) :
    (data.ofLE firstClass secondClass).Z = data.Z := rfl

/-- Reclassification preserves the whole given inclusion natural transformation. -/
theorem ofLE_inclusion_exact (data : FunctorialFactorizationData W₁ W₂)
    (firstClass : W₁ ≤ V₁) (secondClass : W₂ ≤ V₂) :
    (data.ofLE firstClass secondClass).i = data.i := rfl

/-- Reclassification preserves the whole given projection natural transformation. -/
theorem ofLE_projection_exact (data : FunctorialFactorizationData W₁ W₂)
    (firstClass : W₁ ≤ V₁) (secondClass : W₂ ≤ V₂) :
    (data.ofLE firstClass secondClass).p = data.p := rfl

/-- Reclassification keeps every entire given Arrow middle map. -/
theorem ofLE_middle_map_exact (data : FunctorialFactorizationData W₁ W₂)
    (firstClass : W₁ ≤ V₁) (secondClass : W₂ ≤ V₂)
    {f g : Arrow C} (square : f ⟶ g) :
    (data.ofLE firstClass secondClass).Z.map square = data.Z.map square := rfl

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
