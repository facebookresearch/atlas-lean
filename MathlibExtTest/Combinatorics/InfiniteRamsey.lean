/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfiniteRamsey

-- At the smallest positive arity, a coloring of points gives an infinite constant-color set.
example {α ι : Type*} [Finite ι] {X : Set α} (hX : X.Infinite) (f : α → ι) :
    ∃ Y : Set α, Y ⊆ X ∧ Y.Infinite ∧ ∃ c : ι, ∀ x ∈ Y, f x = c := by
  classical
  let χ (s : {s : Finset α // s.card = 1 ∧ (↑s : Set α) ⊆ X}) : ι :=
    f (Finset.card_eq_one.mp s.property.1).choose
  obtain ⟨Y, hYX, hY, c, hc⟩ := MetaMathlibExt.infinite_ramsey hX (by decide) χ
  refine ⟨Y, hYX, hY, c, ?_⟩
  intro x hx
  let s : {s : Finset α // s.card = 1 ∧ (↑s : Set α) ⊆ X} :=
    ⟨{x}, Finset.card_singleton x, by simpa using hYX hx⟩
  have heq : (Finset.card_eq_one.mp s.property.1).choose = x := by
    simp [s]
  simpa [χ, heq] using hc s (by simpa [s] using hx)

-- A two-color consumer can compare arbitrary triples of an infinite subset of `X`.
example {α : Type*} {X : Set α} (hX : X.Infinite)
    (χ : {s : Finset α // s.card = 3 ∧ (↑s : Set α) ⊆ X} → Bool) :
    ∃ Y : Set α, Y ⊆ X ∧ Y.Infinite ∧
      ∀ s t, (↑s.1 : Set α) ⊆ Y → (↑t.1 : Set α) ⊆ Y → χ s = χ t := by
  obtain ⟨Y, hYX, hY, _, hc⟩ := MetaMathlibExt.infinite_ramsey hX (by decide) χ
  exact ⟨Y, hYX, hY, fun s t hs ht ↦ (hc s hs).trans (hc t ht).symm⟩

-- The palette can have just one color, with no restriction on positive arity.
example {α : Type*} {X : Set α} (hX : X.Infinite) {k : ℕ} (hk : 0 < k)
    (χ : {s : Finset α // s.card = k ∧ (↑s : Set α) ⊆ X} → Fin 1) :
    ∃ Y : Set α, Y ⊆ X ∧ Y.Infinite ∧ ∀ s, (↑s.1 : Set α) ⊆ Y → χ s = 0 := by
  obtain ⟨Y, hYX, hY, c, hc⟩ := MetaMathlibExt.infinite_ramsey hX hk χ
  exact ⟨Y, hYX, hY, fun s hs ↦ (hc s hs).trans (Subsingleton.elim c 0)⟩
