/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Limits.TransfiniteSourceUnder
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The SAME native source-under diagram retains genuine well-order continuity

At each actual limit stage, the connected original under-forget functor
creates and reflects the original colimit. Its mapped cocone is precisely
the SAME original native well-order cocone. Category object, Hom and
stage universes remain independent; all original root maps are retained.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.TransfiniteCompositionOfShape
attribute [local instance] IsFiltered.isConnected

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape J f)

/-- The SAME entire original native source-under diagram is genuinely continuous at every
original limit. -/
instance sourceUnderIsWellOrderContinuous : (sourceUnderDiagram c).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    let _ : OrderBot (Set.Iio m) := {
      bot := ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩
      bot_le _ := bot_le }
    have hc : IsColimit ((Under.forget X).mapCocone
        ((Set.principalSegIio m).cocone (sourceUnderDiagram c))) :=
      c.F.isColimitOfIsWellOrderContinuous m hm
    exact ⟨isColimitOfReflects (Under.forget X) hc⟩

end CategoryTheory.TransfiniteCompositionOfShape
