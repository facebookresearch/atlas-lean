/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.InverseTower

/-! # Original-square and singleton clients of inverse-tower lifting

The original prescribed diagonal has both strict factor equations. A maximum
is never subjected to a successor condition; a singleton tower is included.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.MorphismProperty.InverseTowerTest

-- All original prescribed diagonal equations are retained.
lemma original_square {C : Type u} [Category.{v} C]
    (I : MorphismProperty C) {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (D : Jᵒᵖ ⥤ C) [D.rightOp.IsWellOrderContinuous]
    (c : Cone D) (hc : IsLimit c)
    (hsucc : ∀ j : J, ¬IsMax j →
      I.rlp (D.map (homOfLE (Order.le_succ j)).op))
    {A B : C} (i : A ⟶ B) (hi : I i)
    (a : A ⟶ c.pt) (b : B ⟶ D.obj (Opposite.op (⊥ : J)))
    (sq : CommSq a i (c.π.app (Opposite.op (⊥ : J))) b) :
    ∃ l : B ⟶ c.pt, i ≫ l = a ∧ l ≫ c.π.app (Opposite.op (⊥ : J)) = b := by
  let _ : HasLiftingProperty i (c.π.app (Opposite.op (⊥ : J))) :=
    continuous_inverse_tower_rlp I D c hc hsucc i hi
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

-- No impossible successor condition is required at a singleton maximum.
lemma singleton_projection {C : Type u} [Category.{v} C]
    (I : MorphismProperty C) {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] [Subsingleton J]
    (D : Jᵒᵖ ⥤ C) [D.rightOp.IsWellOrderContinuous]
    (c : Cone D) (hc : IsLimit c) :
    I.rlp (c.π.app (Opposite.op (⊥ : J))) := by
  apply continuous_inverse_tower_rlp I D c hc
  intro j hj
  have hmax : IsMax j := by
    intro k hjk
    exact le_of_eq (Subsingleton.elim k j)
  exact (hj hmax).elim

end CategoryTheory.MorphismProperty.InverseTowerTest
