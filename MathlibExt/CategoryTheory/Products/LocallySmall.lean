/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Locally small product categories

The product of two categories locally small at a given universe is locally small
at that universe. The object and Hom universes of the factors are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe s v₁ v₂ u₁ u₂

namespace CategoryTheory.Prod

/-- The product of two locally small categories is locally small at the same bound. -/
theorem locallySmall (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D]
    [hC : LocallySmall.{s} C] [hD : LocallySmall.{s} D] :
    LocallySmall.{s} (C × D) where
  hom_small X Y := by
    change Small.{s} ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2))
    exact @small_prod _ _ (hC.hom_small X.1 Y.1) (hD.hom_small X.2 Y.2)

end CategoryTheory.Prod
