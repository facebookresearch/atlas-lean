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

public import Mathlib.Data.Set.Image
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 359, Logic 360, Logic 405

/-!
# Tukey Reducibility; Tukey equivalence; Cofinal type

## References

* Kunen (for `TukeyLE`)
* Jech (for `TukeyEquiv`, `CofinalType`)
-/

namespace MetaMathlibExt

-- Logic 359: Tukey Reducibility

/-- D ≤_T E if there is a convergent (Tukey) map D → E, one carrying unbounded subsets of
D to unbounded subsets of E.
-/
def TukeyLE (D E : Type) [Preorder D] [Preorder E] : Prop :=
  ∃ f : D → E, ∀ A : Set D, (¬ ∃ b : D, ∀ a ∈ A, a ≤ b) → ¬ ∃ b : E, ∀ a ∈ f '' A, a ≤ b

-- Logic 360: Tukey equivalence

/-- D ≡_T E: cofinal (Tukey) equivalence means Tukey reducibility in both directions. -/
def TukeyEquiv (D E : Type) [Preorder D] [Preorder E] : Prop := TukeyLE D E ∧ TukeyLE E D

-- Logic 405: Cofinal type

/-- A cofinal type is a ≡_T-equivalence class of preordered sets. -/
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

end MetaMathlibExt

end
