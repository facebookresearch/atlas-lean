/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# The actual pushout along a coproduct inclusion

Pushing a map `X → A` along the original left inclusion `X → X ⨿ Y`
gives the same coproduct `A ⨿ Y`. The whole map from the original
coproduct and both pushout legs are retained by the actual universal
property and its chosen-pushout comparison.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CoproductPushout

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  {X A Y : C} (i : X ⟶ A)

/-- The chosen pushout has both whole original map directions to the same actual coproduct. -/
def iso [HasPushout i (coprod.inl : X ⟶ X ⨿ Y)] :
    pushout i (coprod.inl : X ⟶ X ⨿ Y) ≅ A ⨿ Y :=
  (IsPushout.of_coprod_inl_with_id i Y).flip.isoPushout.symm

/-- The full cone-side leg is the same original coproduct inclusion under the actual pushout
chart. -/
@[reassoc]
theorem iso_hom_inl [HasPushout i (coprod.inl : X ⟶ X ⨿ Y)] :
    pushout.inl i (coprod.inl : X ⟶ X ⨿ Y) ≫ (iso i).hom =
      (coprod.inl : A ⟶ A ⨿ Y) :=
  (IsPushout.of_coprod_inl_with_id i Y).flip.inl_isoPushout_inv

/-- The entire original target leg is the same original two-summand map under the pushout chart. -/
@[reassoc]
theorem iso_hom_inr [HasPushout i (coprod.inl : X ⟶ X ⨿ Y)] :
    pushout.inr i (coprod.inl : X ⟶ X ⨿ Y) ≫ (iso i).hom = coprod.map i (𝟙 Y) :=
  (IsPushout.of_coprod_inl_with_id i Y).flip.inr_isoPushout_inv

end CategoryTheory.Limits.CoproductPushout
