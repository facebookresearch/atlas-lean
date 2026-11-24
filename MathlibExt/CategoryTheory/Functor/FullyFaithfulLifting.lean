/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Lifting properties and fully faithful functors

A full faithful functor preserves and reflects the lifting property between
two morphisms in its source category. Essential surjectivity is unnecessary
because every object in the mapped lifting square is already in the image.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uC vC uD vD

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A full faithful functor preserves and reflects the lifting property
between two morphisms in its source category. -/
theorem hasLiftingProperty_map_iff_of_full_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (F.map i) (F.map p) ↔
      HasLiftingProperty i p := by
  constructor
  · intro h
    constructor
    intro f g sq
    obtain ⟨lD⟩ := (h.sq_hasLift (sq.map F)).exists_lift
    let l := F.preimage lD.l
    exact CommSq.HasLift.mk'
      { l := l
        fac_left := by
          apply F.map_injective
          calc
            F.map (i ≫ l) = F.map i ≫ F.map l := F.map_comp i l
            _ = F.map i ≫ lD.l := by rw [F.map_preimage]
            _ = F.map f := lD.fac_left
        fac_right := by
          apply F.map_injective
          calc
            F.map (l ≫ p) = F.map l ≫ F.map p := F.map_comp l p
            _ = lD.l ≫ F.map p := by rw [F.map_preimage]
            _ = F.map g := lD.fac_right }
  · intro h
    constructor
    intro f g sq
    let f' := F.preimage f
    let g' := F.preimage g
    have sq' : CommSq f' i p g' := by
      constructor
      apply F.map_injective
      calc
        F.map (f' ≫ p) = F.map f' ≫ F.map p := F.map_comp f' p
        _ = f ≫ F.map p := by rw [F.map_preimage]
        _ = F.map i ≫ g := sq.w
        _ = F.map i ≫ F.map g' := by rw [F.map_preimage]
        _ = F.map (i ≫ g') := (F.map_comp i g').symm
    obtain ⟨l⟩ := (h.sq_hasLift sq').exists_lift
    exact CommSq.HasLift.mk'
      { l := F.map l.l
        fac_left := by
          calc
            F.map i ≫ F.map l.l = F.map (i ≫ l.l) :=
              (F.map_comp i l.l).symm
            _ = F.map f' := congrArg (fun k => F.map k) l.fac_left
            _ = f := F.map_preimage f
        fac_right := by
          calc
            F.map l.l ≫ F.map p = F.map (l.l ≫ p) :=
              (F.map_comp l.l p).symm
            _ = F.map g' := congrArg (fun k => F.map k) l.fac_right
            _ = g := F.map_preimage g }

end CategoryTheory.Functor
