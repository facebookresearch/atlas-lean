/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.ClosedPowerInterchange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! # Original constant-power compatibility of whole closed interchange

This is an equation between the actual whole native powers. The original
second projection is retained through both counits and the inverse braid.
It supplies no caller-chosen Iso or weak-equivalence outcome.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.ClosedPowerInterchangeOriginalConstant
variable {C : Type u} [Category.{v} C]
  [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- The Cartesian tensor carries the canonical braiding that swaps its two projections. -/
local instance cartesianBraiding : BraidedCategory C := .ofCartesianMonoidalCategory

omit [MonoidalClosed C] in
/-- The exact inverse braid and associators keep the original second-factor
projection, with both remaining Cartesian legs unchanged. -/
@[reassoc]
theorem inverseSwap_snd (A D X : C) :
    (α_ D A X).inv ≫ ((β_ A D).inv ▷ X) ≫ (α_ A D X).hom ≫
        CartesianMonoidalCategory.snd A (D ⊗ X) =
      D ◁ CartesianMonoidalCategory.snd A X := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, associator_hom_snd_fst,
      whiskerRight_fst_assoc, braiding_inv_snd,
      associator_inv_fst_fst, whiskerLeft_fst]
  · simp only [Category.assoc, associator_hom_snd_snd,
      whiskerRight_snd,
      associator_inv_snd, whiskerLeft_snd]

/-- The native whole interchange sends the original constant A-power to the
same original constant A-power of the D-power. Both counits are explicit. -/
theorem interchange_inv_constantPower (A D W : C) :
    (ihom D).map (curry (CartesianMonoidalCategory.snd A W)) ≫
        (ClosedPowerInterchange.interchange A D W).inv =
      curry (CartesianMonoidalCategory.snd A ((ihom D).obj W)) := by
  let c := curry (CartesianMonoidalCategory.snd A W)
  have he : D ◁ (ihom D).map c ≫ (ihom.ev D).app ((ihom A).obj W) =
      (ihom.ev D).app W ≫ c := (ihom.ev D).naturality c
  apply uncurry_injective
  apply uncurry_injective
  conv_rhs => rw [uncurry_curry, uncurry_eq]
  rw [uncurry_natural_left, uncurry_natural_left,
    ClosedPowerInterchange.interchange_inv_double_uncurry,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  dsimp only [c] at he
  rw [← whiskerLeft_comp_assoc, he, whiskerLeft_comp, Category.assoc]
  rw [← uncurry_eq, uncurry_curry, whiskerLeft_snd, inverseSwap_snd_assoc]

end CategoryTheory.ClosedPowerInterchangeOriginalConstant
