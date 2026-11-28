/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.DiscreteCofree
public import MathlibExt.CategoryTheory.Functor.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Enough injectives in diagram categories

Let I and C be categories. Suppose C has pullbacks, products sized to include
the objects and morphisms of I, and enough injectives. Then the category of
diagrams I → C has enough injectives.

Choose an injective presentation at each object and right Kan extend this
discrete family. Restriction preserves and reflects monomorphisms, so the
adjunction supplies a monomorphism into an injective diagram. This construction
applies to arbitrary categories with the stated limits.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
  {C : Type u₂} [Category.{v₂} C]

/-- Pullbacks, products sized to the objects and morphisms of I, and enough injectives in C give
enough injectives in I ⥤ C. -/
theorem enoughInjectives_functorCategory_of_products
    [HasPullbacks C] [HasProducts.{max u₁ v₁} C] [EnoughInjectives C] :
    EnoughInjectives (I ⥤ C) := by
  let : ∀ i : I, HasProductsOfShape (discreteCofreeIndex i) C := fun _ ↦ inferInstance
  let : ∀ V : Discrete I ⥤ C,
      Functor.HasPointwiseRightKanExtension (discreteCofreeInclusion I) V :=
    fun V ↦ discreteCofreeHasPointwiseRightKanExtension C V
  let : ∀ V : Discrete I ⥤ C,
      Functor.HasRightKanExtension (discreteCofreeInclusion I) V := fun _ ↦ inferInstance
  let : EnoughInjectives (Discrete I ⥤ C) := enoughInjectives_discrete I
  let : (discreteCofreeRestriction (I := I) C).PreservesMonomorphisms := inferInstance
  let : (discreteCofreeRestriction (I := I) C).ReflectsMonomorphisms := inferInstance
  exact EnoughInjectives.of_adjunction ((discreteCofreeInclusion I).ranAdjunction C)

end CategoryTheory.Limits
