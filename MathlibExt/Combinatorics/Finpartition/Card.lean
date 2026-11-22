/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `306b05307ce5e07e232dc0c0f350c714e8df4107`.
Original formalization by Tsutomu Okano (@toskua) with Meta Muse;
ported with permission.
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Tauto

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

/-! ### Bell numbers count finpartitions -/

private theorem sdiff_part_eq {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s)
    {a : α} (ha : a ∈ s) :
    s \ P.part a = (s.erase a) \ (P.part a).erase a := by
  have hB : P.part a = insert a ((P.part a).erase a) :=
    (Finset.insert_erase (P.mem_part ha)).symm
  rw [hB]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
  tauto

private def blockProps {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (t : { t : Finset α // t ∈ (s.erase a).powerset }) (d : Finset (Finset α)) : Prop :=
  (∀ p ∈ d, p ⊆ (s.erase a) \ t.val) ∧
  (∀ x ∈ (s.erase a) \ t.val, ∃! q, q ∈ d ∧ x ∈ q) ∧
  ∅ ∉ d

private def rebuild {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (t : { t : Finset α // t ∈ (s.erase a).powerset }) (d : Finset (Finset α))
    (h : blockProps s a t d) : Finpartition ((s.erase a) \ t.val) :=
  Finpartition.ofExistsUnique d h.1 h.2.1 h.2.2

private theorem parts_rebuild {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (t : { t : Finset α // t ∈ (s.erase a).powerset }) (d : Finset (Finset α))
    (h : blockProps s a t d) : (rebuild s a t d h).parts = d := rfl

private def addBlock {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∈ s)
    (t : Finset α) (ht : t ∈ (s.erase a).powerset) (Q : Finpartition ((s.erase a) \ t)) :
    Finpartition s :=
  Finpartition.ofExistsUnique (insert (insert a t) Q.parts)
    (fun p hp => by
      have htsub : t ⊆ s.erase a := Finset.mem_powerset.mp ht
      have hts : t ⊆ s := htsub.trans (Finset.erase_subset a s)
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact Finset.insert_subset_iff.mpr ⟨ha, hts⟩
      · exact (Q.subset hp).trans (Finset.sdiff_subset.trans (Finset.erase_subset a s)))
    (fun x hxs => by
      have htsub : t ⊆ s.erase a := Finset.mem_powerset.mp ht
      have hat : a ∉ t := fun h => Finset.notMem_erase a s (htsub h)
      have haT : a ∉ (s.erase a) \ t :=
        fun h => Finset.notMem_erase a s (Finset.mem_sdiff.mp h).1
      have haQ : ∀ q ∈ Q.parts, a ∉ q := fun q hq haq => haT (Q.subset hq haq)
      by_cases hx : x = a
      · subst x
        refine ⟨insert a t, ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩,
          fun q hq => ?_⟩
        obtain ⟨hq1, hxq⟩ := hq
        rw [Finset.mem_insert] at hq1
        rcases hq1 with rfl | hq1
        · rfl
        · exact absurd hxq (haQ q hq1)
      · by_cases hxt : x ∈ t
        · refine ⟨insert a t, ⟨Finset.mem_insert_self _ _,
            Finset.mem_insert.mpr (Or.inr hxt)⟩, fun q hq => ?_⟩
          obtain ⟨hq1, hxq⟩ := hq
          rw [Finset.mem_insert] at hq1
          rcases hq1 with rfl | hq1
          · rfl
          · have hxT := Q.subset hq1 hxq
            rw [Finset.mem_sdiff] at hxT
            exact absurd hxt hxT.2
        · have hxT : x ∈ (s.erase a) \ t :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hx, hxs⟩, hxt⟩
          obtain ⟨q, ⟨hq, hxq⟩, huniq⟩ := Q.existsUnique_mem hxT
          refine ⟨q, ⟨Finset.mem_insert.mpr (Or.inr hq), hxq⟩, fun p hpp => ?_⟩
          obtain ⟨hpp1, hxp⟩ := hpp
          rw [Finset.mem_insert] at hpp1
          rcases hpp1 with rfl | hpp1
          · rw [Finset.mem_insert] at hxp
            rcases hxp with hxa | hxt'
            · exact absurd hxa hx
            · exact absurd hxt' hxt
          · exact huniq p ⟨hpp1, hxp⟩)
    (by
      rw [Finset.mem_insert]
      rintro (h | h)
      · have hcon := Finset.mem_insert_self a t
        rw [← h] at hcon
        exact Finset.notMem_empty a hcon
      · exact Q.empty_notMem_parts h)

private theorem parts_addBlock {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∈ s) (t : Finset α) (ht : t ∈ (s.erase a).powerset)
    (Q : Finpartition ((s.erase a) \ t)) :
    (addBlock ha t ht Q).parts = insert (insert a t) Q.parts := rfl

private def outerEquiv {α : Type*} [DecidableEq α] (s : Finset α) {a : α} (ha : a ∈ s) :
    Finpartition s ≃ { x : { t : Finset α // t ∈ (s.erase a).powerset } × Finset (Finset α) //
      blockProps s a x.1 x.2 } where
  toFun P :=
    ⟨(⟨(P.part a).erase a,
      Finset.mem_powerset.mpr (Finset.erase_subset_erase a (P.part_subset a))⟩,
      P.parts.erase (P.part a)), by
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_erase] at hp
        rw [← sdiff_part_eq P ha]
        intro x hxp
        rw [Finset.mem_sdiff]
        exact ⟨P.subset hp.2 hxp,
          fun hxB => hp.1 (P.eq_of_mem_parts hp.2 (P.part_mem.2 ha) hxp hxB)⟩
      · intro x hx
        rw [← sdiff_part_eq P ha] at hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨hxs, hxB⟩ := hx
        obtain ⟨p, ⟨hp, hxp⟩, huniq⟩ := P.existsUnique_mem hxs
        have hpB : p ≠ P.part a := fun h => hxB (h ▸ hxp)
        exact ⟨p, ⟨Finset.mem_erase.mpr ⟨hpB, hp⟩, hxp⟩,
          fun q hq => huniq q ⟨Finset.mem_of_mem_erase hq.1, hq.2⟩⟩
      · exact fun h => P.empty_notMem_parts (Finset.mem_of_mem_erase h)⟩
  invFun x := addBlock ha x.val.1.val x.val.1.property
    (rebuild s a x.val.1 x.val.2 x.property)
  left_inv P := by
    apply Finpartition.ext_iff.mpr
    change (addBlock ha ((P.part a).erase a)
      (Finset.mem_powerset.mpr (Finset.erase_subset_erase a (P.part_subset a)))
      (rebuild s a ⟨(P.part a).erase a,
        Finset.mem_powerset.mpr (Finset.erase_subset_erase a (P.part_subset a))⟩
        (P.parts.erase (P.part a)) _)).parts = P.parts
    rw [parts_addBlock, parts_rebuild, Finset.insert_erase (P.mem_part ha),
      Finset.insert_erase (P.part_mem.2 ha)]
  right_inv x := by
    obtain ⟨⟨⟨tval, ht⟩, d⟩, h⟩ := x
    have hat : a ∉ tval :=
      fun hh => Finset.notMem_erase a s ((Finset.mem_powerset.mp ht) hh)
    have hpart : (addBlock ha tval ht (rebuild s a ⟨tval, ht⟩ d h)).part a
        = insert a tval :=
      (addBlock ha tval ht _).part_eq_of_mem (Finset.mem_insert_self _ _)
        (Finset.mem_insert_self _ _)
    have hmem : insert a tval ∉ d := by
      obtain ⟨h1, _, _⟩ := h
      intro hmd
      have haT := h1 _ hmd (Finset.mem_insert_self a tval)
      rw [Finset.mem_sdiff] at haT
      exact Finset.notMem_erase a s haT.1
    apply Subtype.ext
    apply Prod.ext_iff.mpr
    constructor
    · apply Subtype.ext
      change ((addBlock ha tval ht (rebuild s a ⟨tval, ht⟩ d h)).part a).erase a = tval
      rw [hpart, Finset.erase_insert hat]
    · change ((addBlock ha tval ht (rebuild s a ⟨tval, ht⟩ d h)).parts.erase
        ((addBlock ha tval ht (rebuild s a ⟨tval, ht⟩ d h)).part a)) = d
      rw [parts_addBlock, parts_rebuild, hpart]
      exact Finset.erase_insert hmem

private def subtypeProdEquivSigmaSubtype {T D : Type*} (p : T × D → Prop) :
    { x : T × D // p x } ≃ Σ t : T, { d : D // p (t, d) } where
  toFun x := ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
  invFun x := ⟨(x.1, x.2.val), x.2.property⟩
  left_inv x := by obtain ⟨⟨t, d⟩, h⟩ := x; rfl
  right_inv x := by obtain ⟨t, ⟨d, h⟩⟩ := x; rfl

private def fiberEquiv {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (t : { t : Finset α // t ∈ (s.erase a).powerset }) :
    { d : Finset (Finset α) // blockProps s a t d } ≃ Finpartition ((s.erase a) \ t.val) where
  toFun x := rebuild s a t x.val x.property
  invFun Q := ⟨Q.parts, by
    refine ⟨?_, ?_, ?_⟩
    · exact fun p hp => Q.subset hp
    · exact fun x hx => Q.existsUnique_mem hx
    · exact Q.empty_notMem_parts⟩
  left_inv x := by
    obtain ⟨d, h⟩ := x
    apply Subtype.ext
    exact parts_rebuild s a t d h
  right_inv Q := by
    apply Finpartition.ext_iff.mpr
    exact parts_rebuild s a t Q.parts _

set_option linter.style.haveILetI false in
/-- **Bell numbers count set partitions.** The number of partitions of a finite set `s` into
nonempty, pairwise disjoint blocks whose union is `s` (Mathlib's `Finpartition s`, whose parts
exclude `∅`) is the Bell number `Nat.bell (#s)`, where `Nat.bell` is defined by `B 0 = 1` and
`B (n + 1) = ∑ i ≤ n, (n choose i) * B (n - i)`. This is the counting statement left as a TODO
in `Mathlib.Combinatorics.Enumerative.Bell`. -/
theorem card_eq_bell {α : Type*} [DecidableEq α] (s : Finset α) :
    Fintype.card (Finpartition s) = s.card.bell := by
  have hempty : Fintype.card (Finpartition (∅ : Finset α)) = (∅ : Finset α).card.bell := by
    have h1 : Fintype.card (Finpartition (∅ : Finset α)) = 1 := by
      apply Fintype.card_eq_one_iff_nonempty_unique.mpr
      rw [← Finset.bot_eq_empty]
      exact ⟨inferInstance⟩
    calc Fintype.card (Finpartition (∅ : Finset α)) = 1 := h1
      _ = (∅ : Finset α).card.bell := by rw [Finset.card_empty]; exact Nat.bell_zero.symm
  have key : ∀ (n : ℕ) (s : Finset α),
      s.card ≤ n → Fintype.card (Finpartition s) = s.card.bell := by
    intro n
    induction n with
    | zero =>
        intro s hs
        have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
        rw [hs0]
        exact hempty
    | succ n ih =>
        intro s hs
        by_cases hne : s = ∅
        · rw [hne]; exact hempty
        · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
          have hsu : s.card = (s.erase a).card + 1 := by
            have h2 := Finset.card_erase_of_mem ha
            omega
          have hcard : Fintype.card (Finpartition s)
              = ∑ t ∈ (s.erase a).powerset, Fintype.card (Finpartition ((s.erase a) \ t)) := by
            haveI : Fintype { x : { t : Finset α // t ∈ (s.erase a).powerset } ×
                Finset (Finset α) // blockProps s a x.1 x.2 } :=
              Fintype.ofEquiv (Finpartition s) (outerEquiv s ha)
            haveI : ∀ t : { t : Finset α // t ∈ (s.erase a).powerset },
                Fintype { d : Finset (Finset α) // blockProps s a t d } := fun t =>
              Fintype.ofEquiv (Finpartition ((s.erase a) \ t.val)) (fiberEquiv s a t).symm
            calc Fintype.card (Finpartition s)
                = Fintype.card { x : { t : Finset α // t ∈ (s.erase a).powerset } ×
                    Finset (Finset α) // blockProps s a x.1 x.2 } :=
                  Fintype.card_congr (outerEquiv s ha)
              _ = Fintype.card (Σ t : { t : Finset α // t ∈ (s.erase a).powerset },
                    { d : Finset (Finset α) // blockProps s a t d }) :=
                  Fintype.card_congr (subtypeProdEquivSigmaSubtype
                    (fun x : { t : Finset α // t ∈ (s.erase a).powerset } × Finset (Finset α) =>
                      blockProps s a x.1 x.2))
              _ = ∑ t : { t : Finset α // t ∈ (s.erase a).powerset },
                    Fintype.card { d : Finset (Finset α) // blockProps s a t d } :=
                  Fintype.card_sigma
              _ = ∑ t : { t : Finset α // t ∈ (s.erase a).powerset },
                    Fintype.card (Finpartition ((s.erase a) \ t.val)) := by
                  have hfib : ∀ t : { t : Finset α // t ∈ (s.erase a).powerset },
                      Fintype.card { d : Finset (Finset α) // blockProps s a t d }
                      = Fintype.card (Finpartition ((s.erase a) \ t.val)) :=
                    fun t => Fintype.card_congr (fiberEquiv s a t)
                  simp only [hfib]
              _ = ∑ t ∈ (s.erase a).powerset, Fintype.card (Finpartition ((s.erase a) \ t)) :=
                  Finset.sum_coe_sort (s.erase a).powerset
                    (fun t => Fintype.card (Finpartition ((s.erase a) \ t)))
          have hIH : ∀ t ∈ (s.erase a).powerset,
              Fintype.card (Finpartition ((s.erase a) \ t))
              = ((s.erase a).card - t.card).bell := by
            intro t ht
            have hsub : t ⊆ s.erase a := Finset.mem_powerset.mp ht
            have hle : ((s.erase a) \ t).card ≤ n := by
              have h1 : ((s.erase a) \ t).card ≤ (s.erase a).card :=
                Finset.card_le_card Finset.sdiff_subset
              have h2 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
              omega
            have hIHt := ih _ hle
            rw [Finset.card_sdiff_of_subset hsub] at hIHt
            exact hIHt
          rw [hcard]
          trans ∑ t ∈ (s.erase a).powerset, ((s.erase a).card - t.card).bell
          · exact Finset.sum_congr rfl hIH
          · have hfib : ∀ t ∈ (s.erase a).powerset,
                t.card ∈ Finset.range ((s.erase a).card + 1) := by
              intro t ht
              rw [Finset.mem_range]
              exact Nat.lt_succ_of_le (Finset.card_le_card (Finset.mem_powerset.mp ht))
            trans ∑ k ∈ Finset.range ((s.erase a).card + 1),
              ∑ i ∈ (s.erase a).powerset with i.card = k, ((s.erase a).card - i.card).bell
            · exact (Finset.sum_fiberwise_of_maps_to hfib _).symm
            · rw [Nat.range_succ_eq_Iic, hsu, Nat.bell_succ]
              apply Finset.sum_congr rfl
              intro k hk
              rw [← Finset.powersetCard_eq_filter]
              have hconst : ∀ i ∈ Finset.powersetCard k (s.erase a),
                  ((s.erase a).card - i.card).bell = ((s.erase a).card - k).bell := by
                intro i hi
                rw [(Finset.mem_powersetCard.mp hi).2]
              rw [Finset.sum_congr rfl hconst]
              rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, Nat.cast_id]
  exact key s.card s le_rfl


end Finpartition
