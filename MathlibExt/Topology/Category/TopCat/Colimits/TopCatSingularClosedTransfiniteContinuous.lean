/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import
MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfinitePreserves

/-!
# `toSSet` keeps well-order continuity of closed-T1 diagrams

For a well-order-continuous `J`-diagram `F` in `TopCat.{u}` all of whose
transition maps lie in `TopCat.closedT1Embeddings`, the composite
`F ⋙ TopCat.toSSet` is again well-order-continuous. At each successor-limit
stage `m`, the restriction of `F` to `Set.Iio m` inherits the closed-T1
hypothesis, so `TopCat.preservesColimit_toSSet_of_closedT1_transfinite`
applied to that restriction preserves the stage colimit. No global
`PreservesWellOrderContinuousOfShape` instance is claimed.
Base `0134f34afaa0edf9d00ac45102e200aa67e42c5f`.
Scope is exactly one `J`-diagram in `TopCat.{u}` with all maps in
`closedT1Embeddings`. The only order hypotheses beyond those of
`Functor.IsWellOrderContinuous` are `LinearOrder J` and `OrderBot J`; no
`SuccOrder`, `WellFoundedLT`, or global preservation hypothesis is used.
This supplies the per-diagram continuity input for the actual-cardinal horn
closure, eliminating its last global-continuity premise.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace TopCat

variable {J : Type v} [LinearOrder J] [OrderBot J]

/-- A well-order-continuous closed-T1 `J`-diagram stays well-order-continuous
after composition with the singular functor. -/
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
