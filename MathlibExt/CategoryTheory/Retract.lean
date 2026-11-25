/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of split composites

Both maps in a split pair are retracts, in the arrow category, of their
composite. The constructors retain the original maps and splitting equation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

namespace CategoryTheory

/-- If v≫u is the identity, u is an actual Arrow retract of the same u≫v composite. -/
def splitCompositeLeftRetract {C : Type u} [Category.{v} C] {A B : C}
    (u : A ⟶ B) (v : B ⟶ A) (h : v ≫ u = 𝟙 B) : RetractArrow u (u ≫ v) where
  i :=
    { left := 𝟙 A
      right := v
      w := by
        change (𝟙 A) ≫ (u ≫ v) = u ≫ v
        simp only [Category.id_comp] }
  r :=
    { left := 𝟙 A
      right := u
      w := by
        change (𝟙 A) ≫ u = (u ≫ v) ≫ u
        simp only [Category.assoc, h, Category.id_comp, Category.comp_id] }
  retract := by
    ext
    · change (𝟙 A) ≫ (𝟙 A) = 𝟙 A
      exact Category.id_comp _
    · change v ≫ u = 𝟙 B
      exact h

/-- The actual opposite split map v is also an Arrow retract of the same u≫v composite. -/
def splitCompositeRightRetract {C : Type u} [Category.{v} C] {A B : C}
    (u : A ⟶ B) (v : B ⟶ A) (h : v ≫ u = 𝟙 B) : RetractArrow v (u ≫ v) where
  i :=
    { left := v
      right := 𝟙 A
      w := by
        change v ≫ (u ≫ v) = v ≫ (𝟙 A)
        simp only [← Category.assoc, h, Category.id_comp, Category.comp_id] }
  r :=
    { left := u
      right := 𝟙 A
      w := by
        change u ≫ v = (u ≫ v) ≫ (𝟙 A)
        simp only [Category.comp_id] }
  retract := by
    ext
    · change v ≫ u = 𝟙 B
      exact h
    · change (𝟙 A) ≫ (𝟙 A) = 𝟙 A
      exact Category.id_comp _

end CategoryTheory
