/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Lifting properties in under categories

This file relates lifting against the right component of a fixed morphism in
an under category to lifting against every structured version of the target
map.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C]

/-- A base-category map has the right lifting property against the right
component of a fixed under-category map exactly when all of its structured
versions have the corresponding lifting property in the under category. -/
theorem hasLiftingProperty_right_iff_forall
    {K : C} {P Q : Under K} (i : P ⟶ Q)
    {X Y : C} (p : X ⟶ Y) :
    HasLiftingProperty i.right p ↔
      ∀ (t : K ⟶ X), HasLiftingProperty i
        (Under.homMk p rfl : Under.mk t ⟶ Under.mk (t ≫ p)) := by
  constructor
  · intro h t
    refine ⟨fun {top} {bot} sq ↦ ?_⟩
    let sq' := sq.map (Under.forget K)
    dsimp at sq'
    obtain ⟨l⟩ := (h.sq_hasLift sq').exists_lift
    exact CommSq.HasLift.mk'
      { l := Under.homMk l.l (by
          rw [← Under.w i, Category.assoc, l.fac_left, Under.w top])
        fac_left := by
          apply StructuredArrow.hom_ext
          exact l.fac_left
        fac_right := by
          apply StructuredArrow.hom_ext
          exact l.fac_right }
  · intro h
    refine ⟨fun {top} {bot} sq ↦ ?_⟩
    let t : K ⟶ X := P.hom ≫ top
    let p' : Under.mk t ⟶ Under.mk (t ≫ p) := Under.homMk p rfl
    let top' : P ⟶ Under.mk t := Under.homMk top rfl
    let bot' : Q ⟶ Under.mk (t ≫ p) := Under.homMk bot (by
      change Q.hom ≫ bot = (P.hom ≫ top) ≫ p
      calc
        Q.hom ≫ bot = (P.hom ≫ i.right) ≫ bot := by rw [Under.w i]
        _ = P.hom ≫ (i.right ≫ bot) := Category.assoc _ _ _
        _ = P.hom ≫ (top ≫ p) := by rw [sq.w]
        _ = (P.hom ≫ top) ≫ p := (Category.assoc _ _ _).symm)
    have hsq : top' ≫ p' = i ≫ bot' := by
      apply StructuredArrow.hom_ext
      exact sq.w
    let sq' : CommSq top' i p' bot' := ⟨hsq⟩
    let hs : sq'.HasLift := (h t).sq_hasLift sq'
    obtain ⟨l⟩ := hs.exists_lift
    exact CommSq.HasLift.mk'
      { l := l.l.right
        fac_left := by
          simpa [top'] using congrArg (fun z ↦ z.right) l.fac_left
        fac_right := by
          simpa [p', bot'] using congrArg (fun z ↦ z.right) l.fac_right }

end CategoryTheory.Under

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

/-- A genuine underlying square lift induces a whole lift under the same fixed object. -/
lemma CommSq.HasLift.under {A B X Y : Under S}
    {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y} {sq : CommSq t i p b}
    [CommSq.HasLift (f := t.right) (i := i.right) (p := p.right) (g := b.right)
      (sq.map (Under.forget S))] : sq.HasLift := by
  let sq' := sq.map (Under.forget S)
  dsimp at sq'
  refine ⟨⟨{
    l := Under.homMk sq'.lift ?_
    fac_left := Under.UnderMorphism.ext sq'.fac_left
    fac_right := Under.UnderMorphism.ext sq'.fac_right
  }⟩⟩
  rw [← Under.w i, Category.assoc, sq'.fac_left, Under.w t]

/-- Genuine underlying lifting properties induce the same entire lifting property in the coslice. -/
lemma HasLiftingProperty.under {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [HasLiftingProperty i.right p.right] : HasLiftingProperty i p :=
  ⟨fun _ => .under⟩

end CategoryTheory
