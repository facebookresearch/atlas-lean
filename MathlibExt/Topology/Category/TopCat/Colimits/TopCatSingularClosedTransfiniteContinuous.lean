/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import
MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfinitePreserves

/-!
# Singular complexes preserve closed-diagram order continuity

Let J be a linear order with a least element. Suppose F:J→TopCat is well-order-continuous and
all its transition maps are closed T1-embeddings. Applying the singular-complex functor
preserves this continuity: at each successor-limit stage, the cocone of preceding singular
stages is colimiting at that stage.

A closed T1-embedding is a closed embedding whose codomain singleton is closed at every point
outside the image. The order and space universes v,u are independent.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace TopCat

variable {J : Type v} [LinearOrder J] [OrderBot J]

/-- Let J be a linear order with a least element in universe v, and F:J→TopCat.{u} a diagram whose
every transition map is a closed embedding with closed codomain singletons outside its image. If
F is well-order-continuous, then its composite with the singular-complex functor is
well-order-continuous, preserving the colimit cocones at successor-limit indices. -/
theorem isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite
    {F : J ⥤ TopCat.{u}} [F.IsWellOrderContinuous]
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (F.map f)) :
    (F ⋙ toSSet.{u}).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    have : OrderBot (Set.Iio m) :=
      { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩
        bot_le := fun ⟨_, _⟩ => bot_le }
    have hFm : ∀ ⦃i j : Set.Iio m⦄ (f : i ⟶ j), closedT1Embeddings
        (((Set.principalSegIio m).monotone.functor ⋙ F).map f) :=
      fun _ _ f => hF _
    have := preservesColimit_toSSet_of_closedT1_transfinite
      (F := (Set.principalSegIio m).monotone.functor ⋙ F) hFm
    exact ⟨isColimitOfPreserves toSSet
      (F.isColimitOfIsWellOrderContinuous m hm)⟩

end TopCat
