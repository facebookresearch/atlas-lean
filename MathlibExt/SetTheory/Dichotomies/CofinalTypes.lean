/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 359, Logic 360, Logic 405
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 359: Tukey Reducibility
def TukeyLE (D E : Type) [Preorder D] [Preorder E] : Prop :=
  ∃ f : D → E, ∀ A : Set D, (¬ ∃ b : D, ∀ a ∈ A, a ≤ b) → ¬ ∃ b : E, ∀ a ∈ f '' A, a ≤ b


theorem tukeyLE_refl (D : Type) [Preorder D] : TukeyLE D D :=
  ⟨id, fun A hA => by rwa [Set.image_id]⟩


theorem tukeyLE_trans {D E F : Type} [Preorder D] [Preorder E] [Preorder F]
    (hDE : TukeyLE D E) (hEF : TukeyLE E F) : TukeyLE D F := by
  obtain ⟨f, hf⟩ := hDE
  obtain ⟨g, hg⟩ := hEF
  refine ⟨g ∘ f, fun A hA => ?_⟩
  have himg : (g ∘ f) '' A = g '' (f '' A) := by rw [Set.image_comp]
  rw [himg]
  exact hg (f '' A) (hf A hA)


theorem tukeyLE_of_bounded {D E : Type} [Preorder D] [Preorder E] [Nonempty E]
    (hD : ∀ A : Set D, ∃ b : D, ∀ a ∈ A, a ≤ b) : TukeyLE D E := by
  refine ⟨fun _ => Classical.arbitrary E, fun A hA => absurd (hD A) ?_⟩
  simpa using hA


theorem punit_bounded (A : Set PUnit) : ∃ b : PUnit, ∀ a ∈ A, a ≤ b :=
  ⟨PUnit.unit, fun a _ => le_of_eq (Subsingleton.elim a PUnit.unit)⟩

def TukeyEquiv (D E : Type) [Preorder D] [Preorder E] : Prop := TukeyLE D E ∧ TukeyLE E D

def CofinalType : Type 1 :=
  Quotient (α := Σ D : Type, Preorder D)
    { r := fun X Y => @TukeyEquiv X.1 Y.1 X.2 Y.2
      iseqv := by
        refine ⟨fun X => ⟨⟨id, fun A hA => by rwa [Set.image_id]⟩,
                          ⟨id, fun A hA => by rwa [Set.image_id]⟩⟩,
                fun h => ⟨h.2, h.1⟩, fun h1 h2 => ⟨?_, ?_⟩⟩
        · obtain ⟨f, hf⟩ := h1.1
          obtain ⟨g, hg⟩ := h2.1
          exact ⟨g ∘ f, fun A hA => by rw [Set.image_comp]; exact hg (f '' A) (hf A hA)⟩
        · obtain ⟨f, hf⟩ := h2.2
          obtain ⟨g, hg⟩ := h1.2
          exact ⟨g ∘ f, fun A hA => by rw [Set.image_comp]; exact hg (f '' A) (hf A hA)⟩ }


theorem cofinalType_eq_iff (X Y : Σ D : Type, Preorder D) :
    (Quotient.mk _ X : CofinalType) = Quotient.mk _ Y ↔ @TukeyEquiv X.1 Y.1 X.2 Y.2 :=
  Quotient.eq

end
