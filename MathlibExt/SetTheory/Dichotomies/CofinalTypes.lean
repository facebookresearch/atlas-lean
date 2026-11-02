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

/-- **Tukey reducibility.** For preordered sets $D$ and $E$, $D$ is Tukey reducible to $E$,
written $D \le_T E$, if there is a map $f \colon D \to E$ that carries unbounded sets to
unbounded sets: for every $A \subseteq D$ with no upper bound in $D$, the image $f[A]$ has no
upper bound in $E$.
-/
def TukeyLE (D E : Type) [Preorder D] [Preorder E] : Prop :=
  ∃ f : D → E, ∀ A : Set D, (¬ ∃ b : D, ∀ a ∈ A, a ≤ b) → ¬ ∃ b : E, ∀ a ∈ f '' A, a ≤ b

-- Logic 360: Tukey equivalence

/-- **Tukey equivalence.** Preordered sets $D$ and $E$ are Tukey equivalent (cofinally
equivalent), written $D \equiv_T E$, if $D \le_T E$ and $E \le_T D$, where $\le_T$ is Tukey
reducibility.
-/
def TukeyEquiv (D E : Type) [Preorder D] [Preorder E] : Prop := TukeyLE D E ∧ TukeyLE E D

-- Logic 405: Cofinal type

/-- **Cofinal type.** A cofinal type is an equivalence class of preordered sets under Tukey
equivalence $\equiv_T$, where $D \equiv_T E$ means $D \le_T E$ and $E \le_T D$ (Tukey
reducibility in both directions).
-/
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
