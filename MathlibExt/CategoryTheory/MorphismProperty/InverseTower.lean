/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.Limits.Opposites

/-! # Compatible right lifting along a continuous inverse tower

The original projection of a limiting cone has the right lifting property
against any original class of arrows when every nonmaximal successor map
does. Continuity is the actual well-order continuity of the opposite diagram.
Object, morphism and indexing universes are independent. The proof uses the
native continuous transfinite lifting theorem on the opposite category; no
smallness, model, finiteness or new recursive construction is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.MorphismProperty

/-- The native continuous transfinite lifting theorem, used on the opposite category.
The original continuity cone and its two strict lift equations are retained. -/
lemma continuous_inverse_tower_rlp {C : Type u} [Category.{v} C]
    (I : MorphismProperty C) {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (D : Jᵒᵖ ⥤ C) [D.rightOp.IsWellOrderContinuous]
    (c : Cone D) (hc : IsLimit c)
    (hsucc : ∀ j : J, ¬IsMax j →
      I.rlp (D.map (homOfLE (Order.le_succ j)).op)) :
    I.rlp (c.π.app (Opposite.op (⊥ : J))) := by
  intro A B i hi
  let co := coconeRightOpOfCone c
  have hco : IsColimit co := isColimitCoconeRightOpOfCone D hc
  have hop : ∀ j : J, ¬IsMax j →
      HasLiftingProperty (D.rightOp.map (homOfLE (Order.le_succ j))) i.op := by
    intro j hj
    exact (hsucc j hj i hi).op
  have hl : HasLiftingProperty (co.ι.app (⊥ : J)) i.op :=
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := hco) hop
  simpa only [co, coconeRightOpOfCone, NatTrans.rightOp_app, Quiver.Hom.unop_op] using hl.unop

end CategoryTheory.MorphismProperty
