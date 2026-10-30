/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `306b05307ce5e07e232dc0c0f350c714e8df4107`.
Original formalization by Tsutomu Okano (@toskua) with Avocado (internal agent
identity); ported with permission.
-/

module

public import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

open Finset Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

namespace Finpartition

/-- Product of a weight function over the block cardinalities of a partition. -/
def cardProd {R : Type*} [CommMonoid R] (P : Finpartition s) (f : ℕ → R) : R :=
  ∏ B ∈ P.parts, f B.card

@[simp]
theorem cardProd_empty {R : Type*} [CommMonoid R] {P : Finpartition (∅ : Finset α)}
    (f : ℕ → R) : P.cardProd f = 1 := by
  have h : P.parts = ∅ := parts_eq_empty_iff.mpr rfl
  simp [cardProd, h]

/-- Every block of a finite-set partition is bounded by the carrier cardinality. -/
theorem card_le_of_mem_parts (P : Finpartition s) {B : Finset α} (hB : B ∈ P.parts) :
    B.card ≤ s.card :=
  card_le_card (P.subset hB)

/-- Every block of a finite-set partition has cardinality at least one. -/
theorem one_le_card_of_mem_parts (P : Finpartition s) {B : Finset α}
    (hB : B ∈ P.parts) : 1 ≤ B.card := by
  have hne : B.Nonempty := P.nonempty_of_mem_parts hB
  exact one_le_card.mpr hne

/-!
### Top recognition and strict bound
-/

private theorem top_parts_eq_singleton_of_ne_bot {s : Finset α}
    (hs : s ≠ ⊥) : (⊤ : Finpartition s).parts = {s} := by
  have hsub : (⊤ : Finpartition s).parts ⊆ {s} := parts_top_subset s
  have hmem : s ∈ (⊤ : Finpartition s).parts := by
    obtain ⟨a, ha⟩ := parts_nonempty (⊤ : Finpartition s) hs
    have ha_eq : a = s := mem_singleton.mp (hsub ha)
    rwa [ha_eq] at ha
  rw [eq_singleton_iff_unique_mem]
  exact ⟨hmem, fun t ht => mem_singleton.mp (hsub ht)⟩

private theorem parts_eq_singleton_of_mem_eq_carrier {s : Finset α}
    (P : Finpartition s) {B : Finset α} (hB : B ∈ P.parts) (hBs : B = s) :
    P.parts = {s} := by
  have h_s_mem : s ∈ P.parts := hBs ▸ hB
  rw [eq_singleton_iff_unique_mem]
  constructor
  · exact h_s_mem
  · intro C hC
    by_cases heq : C = B
    · rw [heq, hBs]
    · exfalso
      have hC_sub : C ⊆ s := P.subset hC
      have hC_sub_B : C ⊆ B := hBs ▸ hC_sub
      have h_disj : Disjoint B C := P.disjoint hB hC (Ne.symm heq)
      have hC_le_bot : C ≤ (⊥ : Finset α) := h_disj hC_sub_B le_rfl
      have hC_eq_bot : C = ⊥ := le_antisymm hC_le_bot bot_le
      exact P.bot_notMem (hC_eq_bot ▸ hC)

private theorem eq_top_of_mem_eq_s (P : Finpartition s) {B : Finset α}
    (hB : B ∈ P.parts) (hBs : B = s) : P = ⊤ := by
  by_cases hs : s = ⊥
  · have h_parts_empty : P.parts = ∅ := parts_eq_empty_iff.mpr hs
    rw [h_parts_empty] at hB
    exact absurd hB (notMem_empty B)
  · have h_parts_eq : P.parts = {s} := parts_eq_singleton_of_mem_eq_carrier P hB hBs
    have h_top_parts : (⊤ : Finpartition s).parts = {s} :=
      top_parts_eq_singleton_of_ne_bot hs
    exact Finpartition.ext (by rw [h_parts_eq, h_top_parts])

/-- If `P ≠ ⊤`, every block has cardinality strictly below the carrier. -/
theorem card_lt_of_ne_top (P : Finpartition s) (h_ne_top : P ≠ ⊤)
    {B : Finset α} (hB : B ∈ P.parts) : B.card < s.card := by
  by_cases hs : s = ⊥
  · have h_parts_empty : P.parts = ∅ := parts_eq_empty_iff.mpr hs
    rw [h_parts_empty] at hB
    exact absurd hB (notMem_empty B)
  · by_contra h_not_lt
    have h_le : s.card ≤ B.card := Nat.le_of_not_lt h_not_lt
    have h_B_sub : B ⊆ s := P.subset hB
    have h_B_le : B.card ≤ s.card := card_le_card h_B_sub
    have h_eq_card : B.card = s.card := Nat.le_antisymm h_B_le h_le
    have h_eq : B = s :=
      eq_of_subset_of_card_le h_B_sub (le_of_eq h_eq_card.symm)
    have h_parts_eq : P.parts = {s} := parts_eq_singleton_of_mem_eq_carrier P hB h_eq
    have h_top_parts : (⊤ : Finpartition s).parts = {s} :=
      top_parts_eq_singleton_of_ne_bot hs
    have h_ext : P = ⊤ := by
      apply Finpartition.ext
      rw [h_parts_eq, h_top_parts]
    exact h_ne_top h_ext

/-- A partition of a nonempty carrier is top iff it has one block. -/
theorem eq_top_iff_card_parts_eq_one (P : Finpartition s) (hs : s.Nonempty) :
    P = ⊤ ↔ P.parts.card = 1 := by
  constructor
  · intro h
    have hs' : s ≠ ⊥ := by
      intro hbot
      rw [bot_eq_empty] at hbot
      exact hs.ne_empty hbot
    rw [h, top_parts_eq_singleton_of_ne_bot hs', card_singleton]
  · intro h_card
    have h_nonempty : P.parts.Nonempty := by
      rw [← card_pos, h_card]
      exact Nat.zero_lt_one
    obtain ⟨B, hB⟩ := h_nonempty
    have h_single : P.parts = {B} := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card
      have hB_eq : B = a := mem_singleton.mp (ha ▸ hB)
      calc P.parts = {a} := ha
        _ = {B} := by rw [hB_eq]
    have h_sup : P.parts.sup id = s := P.sup_parts
    rw [h_single] at h_sup
    simp only [sup_singleton] at h_sup
    exact eq_top_of_mem_eq_s P hB h_sup

/-!
### Bottom recognition and general bounds
-/

theorem card_parts_pos_iff (P : Finpartition s) :
    0 < P.parts.card ↔ s.Nonempty := by
  rw [card_pos, parts_nonempty_iff, nonempty_iff_ne_empty, Ne, bot_eq_empty]

theorem one_le_card_parts_of_nonempty (P : Finpartition s) (hs : s.Nonempty) :
    1 ≤ P.parts.card :=
  (card_parts_pos_iff P).mpr hs

/-- A partition is bottom iff its number of blocks equals the carrier cardinality. -/
theorem eq_bot_iff_card_parts_eq_card (P : Finpartition s) :
    P = ⊥ ↔ P.parts.card = s.card := by
  constructor
  · intro h
    rw [h, card_bot]
  · intro h_eq
    have h_sum : ∑ B ∈ P.parts, B.card = s.card := sum_card_parts P
    have h_one_le : ∀ B ∈ P.parts, 1 ≤ B.card := fun B hB =>
      one_le_card_of_mem_parts P hB
    have h_all_one : ∀ B ∈ P.parts, B.card = 1 := by
      intro B hB
      by_contra h_ne_one
      have h_one : 1 ≤ B.card := h_one_le B hB
      have h_ge_two : 2 ≤ B.card := by omega
      have h_erase_card : (P.parts.erase B).card = P.parts.card - 1 :=
        card_erase_of_mem hB
      have h_sum_erase_le : (P.parts.erase B).card ≤ ∑ C ∈ P.parts.erase B, C.card := by
        have h_le : ∀ C ∈ P.parts.erase B, 1 ≤ C.card := fun C hC =>
          one_le_card_of_mem_parts P (mem_of_mem_erase hC)
        have h := card_nsmul_le_sum (P.parts.erase B) (fun C => C.card) 1 h_le
        simpa using h
      have h_sum_eq : ∑ C ∈ P.parts, C.card = B.card + ∑ C ∈ P.parts.erase B, C.card := by
        rw [← add_sum_erase _ _ hB]
      have h_ge : s.card ≥ P.parts.card + 1 := by
        have h1 : B.card + (P.parts.erase B).card ≤ B.card + ∑ C ∈ P.parts.erase B, C.card :=
          Nat.add_le_add_left h_sum_erase_le B.card
        calc s.card = ∑ C ∈ P.parts, C.card := h_sum.symm
          _ = B.card + ∑ C ∈ P.parts.erase B, C.card := h_sum_eq
          _ ≥ B.card + (P.parts.erase B).card := h1
          _ = B.card + (P.parts.card - 1) := by rw [h_erase_card]
          _ ≥ 2 + (P.parts.card - 1) := by
                apply Nat.add_le_add_right h_ge_two
          _ = P.parts.card + 1 := by
                have h_card_pos : 0 < P.parts.card := by
                  rw [card_pos]
                  exact ⟨B, hB⟩
                omega
      omega
    have h_bot_parts_subset : (⊥ : Finpartition s).parts ⊆ P.parts := by
      intro t ht
      rw [parts_bot] at ht
      rw [mem_map] at ht
      obtain ⟨a, ha_mem, ha_eq⟩ := ht
      have h_emb_singleton : (⟨singleton, singleton_injective⟩ : α ↪ Finset α) a = {a} := rfl
      rw [← ha_eq, h_emb_singleton]
      obtain ⟨B, hB_mem, ha_in_B⟩ := P.exists_mem ha_mem
      have hB_card_one : B.card = 1 := h_all_one B hB_mem
      rw [card_eq_one] at hB_card_one
      obtain ⟨x, hx⟩ := hB_card_one
      have ha_eq_x : a = x := by
        rw [hx] at ha_in_B
        rw [mem_singleton] at ha_in_B
        exact ha_in_B
      have hB_eq : B = {a} := by rw [hx, ha_eq_x]
      rw [← hB_eq]
      exact hB_mem
    have h_cards_eq : (⊥ : Finpartition s).parts.card = P.parts.card := by
      rw [card_bot, h_eq]
    have h_eq_parts : P.parts = (⊥ : Finpartition s).parts := by
      have h_le : P.parts.card ≤ (⊥ : Finpartition s).parts.card := by rw [h_cards_eq]
      exact (eq_of_subset_of_card_le h_bot_parts_subset h_le).symm
    exact Finpartition.ext (by rw [h_eq_parts])

@[simp]
theorem cardProd_bot {R : Type*} [CommMonoid R] (f : ℕ → R) (s : Finset α) :
    (⊥ : Finpartition s).cardProd f = (f 1) ^ s.card := by
  unfold cardProd
  rw [parts_bot]
  let e : α ↪ Finset α := ⟨singleton, singleton_injective⟩
  have h_one : ∀ a ∈ s, f (card (e a)) = f 1 := by
    intro a _
    simp [e]
  calc ∏ a ∈ s.map ⟨singleton, singleton_injective⟩, f (card a)
      = ∏ a ∈ s.map e, f (card a) := rfl
    _ = ∏ a ∈ s, f (card (e a)) := by rw [prod_map]
    _ = ∏ _ ∈ s, f 1 := by apply prod_congr rfl h_one
    _ = (f 1) ^ s.card := by rw [prod_const]

theorem cardProd_top {R : Type*} [CommMonoid R] (hs : s.Nonempty) (f : ℕ → R) :
    (⊤ : Finpartition s).cardProd f = f s.card := by
  have hs' : s ≠ ⊥ := by
    intro h
    rw [bot_eq_empty] at h
    exact hs.ne_empty h
  rw [cardProd, top_parts_eq_singleton_of_ne_bot hs', prod_singleton]

/-- `cardProd` commutes with monoid homomorphisms. -/
theorem cardProd_mapMonoidHom {R S : Type*} [CommMonoid R] [CommMonoid S]
    (P : Finpartition s) (f : ℕ → R) (g : R →* S) :
    g (P.cardProd f) = P.cardProd (g ∘ f) := by
  simp [cardProd, map_prod]

end Finpartition
