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

public import MathlibExt.SetTheory.Dichotomies.CofinalTypes
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExtTest.SetTheory.Dichotomies.CofinalTypes

open MetaMathlibExt

-- Logic 359: Tukey Reducibility

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

/-- **What the degenerate entry `1` means.**  Out of a bounded order the condition is empty. -/

theorem tukeyLE_of_bounded {D E : Type} [Preorder D] [Preorder E] [Nonempty E]
    (hD : ∀ A : Set D, ∃ b : D, ∀ a ∈ A, a ≤ b) : TukeyLE D E := by
  refine ⟨fun _ => Classical.arbitrary E, fun A hA => absurd (hD A) ?_⟩
  simpa using hA

/-- Every subset of `PUnit` is bounded, so `PUnit` is the bounded order par excellence. -/

theorem punit_bounded (A : Set PUnit) : ∃ b : PUnit, ∀ a ∈ A, a ≤ b :=
  ⟨PUnit.unit, fun a _ => le_of_eq (Subsingleton.elim a PUnit.unit)⟩

/-- **Not trivial**: `ω` is not Tukey-below `1`, since `ℕ` is unbounded in itself while every
subset of `PUnit` is bounded.  So the first two entries of Todorcevic's list are distinct. -/

theorem not_tukeyLE_nat_punit : ¬ TukeyLE ℕ PUnit := by
  rintro ⟨f, hf⟩
  have hunb : ¬ ∃ b : ℕ, ∀ a ∈ (Set.univ : Set ℕ), a ≤ b := by
    rintro ⟨b, hb⟩
    exact absurd (hb (b + 1) (Set.mem_univ _)) (by omega)
  exact hf Set.univ hunb ⟨PUnit.unit, fun a _ => le_of_eq (Subsingleton.elim a PUnit.unit)⟩

-- Logic 360: Tukey equivalence

/-- **Not trivial**: `ω` and `1` are distinct cofinal types, so Todorcevic's list of five is not
redundant at its first two entries. -/

theorem not_tukeyEquiv_nat_punit : ¬ TukeyEquiv ℕ PUnit := by
  rintro ⟨⟨f, hf⟩, -⟩
  have hunb : ¬ ∃ b : ℕ, ∀ a ∈ (Set.univ : Set ℕ), a ≤ b := by
    rintro ⟨b, hb⟩
    exact absurd (hb (b + 1) (Set.mem_univ _)) (by omega)
  exact hf Set.univ hunb ⟨PUnit.unit, fun a _ => le_of_eq (Subsingleton.elim a PUnit.unit)⟩

-- Logic 405: Cofinal type

/-- **The quotient really is by `≡_T`** — this is what makes "a cofinal type is an equivalence
class of this relation" a true statement about `CofinalType` rather than a hope. -/

theorem cofinalType_eq_iff (X Y : Σ D : Type, Preorder D) :
    (Quotient.mk _ X : CofinalType) = Quotient.mk _ Y ↔ @TukeyEquiv X.1 Y.1 X.2 Y.2 :=
  Quotient.eq

end MathlibExtTest.SetTheory.Dichotomies.CofinalTypes

end
