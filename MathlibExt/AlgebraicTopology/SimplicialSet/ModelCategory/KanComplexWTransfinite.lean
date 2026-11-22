/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWColimits

/-!
# Transfinite weak-equivalence closure from a Kan bottom stage

For an actual well-order-continuous transfinite diagram of weak equivalences
between Kan complexes, a Kan bottom stage supplies the identity used by
successor/limit induction. The result includes shapes with a largest element.
The object and morphism universes of the shape are bounded by the simplicial
universe through `UnivLE`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits

namespace SSet.KanComplex.W

/-- An actual transfinite composition of Kan weak equivalences is a Kan weak
equivalence when its bottom stage is Kan and the shape universe is no larger
than the simplicial universe. -/
theorem of_transfiniteCompositionOfShape_of_kan_bot
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [UnivLE.{v, u}]
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : (SSet.KanComplex.W : MorphismProperty SSet.{u}).TransfiniteCompositionOfShape
      J f)
    [SSet.KanComplex (h.F.obj ⊥)] :
    SSet.KanComplex.W f := by
  have hfrom : ∀ j : J,
      SSet.KanComplex.W
        (h.F.map (homOfLE bot_le : ⊥ ⟶ j)) := by
    intro j
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
        obtain rfl := hj.eq_bot
        simpa using (SSet.KanComplex.W.id (X := h.F.obj ⊥))
    | succ j hj ih =>
        rw [← homOfLE_comp bot_le (Order.le_succ j), h.F.map_comp]
        exact SSet.KanComplex.W.comp ih (h.map_mem j hj)
    | isSuccLimit j hj ih =>
        let _ : OrderBot (Set.Iio j) :=
          { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj⟩
            bot_le _ := bot_le }
        exact MorphismProperty.colimitsOfShape_le _
          (.of_isColimit
            (h.F.isColimitOfIsWellOrderContinuous j hj)
            (fun k ↦ ih _ k.2))
  let g : h.F.obj ⊥ ⟶ Y := h.incl.app ⊥
  have hg : SSet.KanComplex.W g :=
    MorphismProperty.colimitsOfShape_le _
      (.of_isColimit h.isColimit (fun j ↦ hfrom j))
  let e : Arrow.mk f ≅ Arrow.mk g :=
    Arrow.isoMk h.isoBot.symm (Iso.refl _) (by simp [g, h.fac])
  exact (MorphismProperty.arrow_mk_iso_iff SSet.KanComplex.W e).2 hg

end SSet.KanComplex.W
