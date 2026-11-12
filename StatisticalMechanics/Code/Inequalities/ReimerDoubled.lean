/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.Inequalities.ReimerStep
import Mathlib.Combinatorics.SetFamily.Compression.UV

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]











noncomputable def dbl (S T : Finset α) : Finset (α ⊕ α) :=
  S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ T.map ⟨Sum.inr, Sum.inr_injective⟩


@[simp] lemma mem_dbl_inl (S T : Finset α) (a : α) : (Sum.inl a) ∈ dbl S T ↔ a ∈ S := by
  simp [dbl, Finset.mem_union, Finset.mem_map]


@[simp] lemma mem_dbl_inr (S T : Finset α) (a : α) : (Sum.inr a) ∈ dbl S T ↔ a ∈ T := by
  simp [dbl, Finset.mem_union, Finset.mem_map]


lemma mem_dbl (S T : Finset α) (x : α ⊕ α) :
    x ∈ dbl S T ↔ Sum.elim (· ∈ S) (· ∈ T) x := by
  cases x with
  | inl a => simp [mem_dbl_inl S T a]
  | inr a => simp [mem_dbl_inr S T a]




lemma dbl_injective : Function.Injective (fun p : Finset α × Finset α => dbl p.1 p.2) := by
  rintro ⟨S, T⟩ ⟨S', T'⟩ h
  simp only at h
  have hS : S = S' := by ext a; rw [← mem_dbl_inl S T a, ← mem_dbl_inl S' T' a, h]
  have hT : T = T' := by ext a; rw [← mem_dbl_inr S T a, ← mem_dbl_inr S' T' a, h]
  rw [hS, hT]


lemma dbl_injOn (s : Set (Finset α × Finset α)) :
    Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) s :=
  dbl_injective.injOn




lemma image_collapse_dbl (S T : Finset α) :
    (dbl S T).image (Sum.elim id id) = S ∪ T := by
  ext a
  simp only [dbl, Finset.mem_image, Finset.mem_union, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, rfl⟩
    cases x with
    | inl s => rcases hx with (⟨s', hs', h⟩ | ⟨t', ht', h⟩) <;> simp_all
    | inr t => rcases hx with (⟨s', hs', h⟩ | ⟨t', ht', h⟩) <;> simp_all
  · rintro (ha | ha)
    · exact ⟨Sum.inl a, Or.inl ⟨a, ha, rfl⟩, rfl⟩
    · exact ⟨Sum.inr a, Or.inr ⟨a, ha, rfl⟩, rfl⟩










noncomputable def boxDoubled (𝒜 ℬ : Finset (Finset α)) : Finset (Finset (α ⊕ α)) :=
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).image (fun p => dbl p.1 p.2)


lemma mem_boxDoubled (𝒜 ℬ : Finset (Finset α)) (U : Finset (α ⊕ α)) :
    U ∈ boxDoubled 𝒜 ℬ ↔ ∃ S ∈ 𝒜, ∃ T ∈ ℬ, Disjoint S T ∧ dbl S T = U := by
  unfold boxDoubled
  simp only [mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨S, T, ⟨⟨hS, hT⟩, hd⟩, rfl⟩; exact ⟨S, hS, T, hT, hd, rfl⟩
  · rintro ⟨S, hS, T, hT, hd, rfl⟩; exact ⟨S, T, ⟨⟨hS, hT⟩, hd⟩, rfl⟩




theorem card_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := by
  unfold boxDoubled
  exact Finset.card_image_of_injOn (dbl_injOn _)






theorem boxFamily_eq_image_collapse_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    boxFamily 𝒜 ℬ = (boxDoubled 𝒜 ℬ).image (fun U => U.image (Sum.elim id id)) := by
  ext U
  simp only [mem_boxFamily, mem_image, mem_boxDoubled]
  constructor
  · rintro ⟨S, hS, T, hT, hd, rfl⟩
    exact ⟨dbl S T, ⟨S, hS, T, hT, hd, rfl⟩, image_collapse_dbl S T⟩
  · rintro ⟨V, ⟨S, hS, T, hT, hd, rfl⟩, rfl⟩
    exact ⟨S, hS, T, hT, hd, (image_collapse_dbl S T).symm⟩


theorem card_boxFamily_le_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    (boxFamily 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card := by
  rw [boxFamily_eq_image_collapse_boxDoubled]
  exact card_image_le



theorem card_boxDoubled_le_mul (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
  rw [card_boxDoubled]
  calc ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card
      ≤ (𝒜 ×ˢ ℬ).card := card_filter_le _ _
    _ = 𝒜.card * ℬ.card := card_product _ _










noncomputable def upComp (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) : Finset (Finset (α ⊕ α)) :=
  UV.compression {a} ∅ 𝒜


@[simp] theorem upComp_card (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (upComp a 𝒜).card = 𝒜.card := by
  unfold upComp; exact UV.card_compression _ _ _


@[simp] theorem upComp_idem (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) :
    upComp a (upComp a 𝒜) = upComp a 𝒜 := by
  unfold upComp; exact UV.compression_idem _ _ _


noncomputable def downLeft (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Finset (Finset (α ⊕ α)) :=
  Down.compression (Sum.inl i) 𝒜


noncomputable def upRight (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Finset (Finset (α ⊕ α)) :=
  upComp (Sum.inr i) 𝒜


@[simp] theorem downLeft_card (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (downLeft i 𝒜).card = 𝒜.card := by
  unfold downLeft; exact Down.card_compression _ _


@[simp] theorem upRight_card (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (upRight i 𝒜).card = 𝒜.card := by
  unfold upRight; exact upComp_card _ _




noncomputable def doubleCompress (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    Finset (Finset (α ⊕ α)) :=
  upRight i (downLeft i 𝒜)





@[simp] theorem doubleCompress_card (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (doubleCompress i 𝒜).card = 𝒜.card := by
  unfold doubleCompress
  rw [upRight_card, downLeft_card]










def IsDownAtLeft (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Prop :=
  ∀ s ∈ 𝒜, s.erase (Sum.inl i) ∈ 𝒜



def IsUpAtRight (i : α) (𝒜 : Finset (Finset (α ⊕ α))) : Prop :=
  ∀ s ∈ 𝒜, insert (Sum.inr i) s ∈ 𝒜


theorem downLeft_eq_self (i : α) {𝒜 : Finset (Finset (α ⊕ α))} (h : IsDownAtLeft i 𝒜) :
    downLeft i 𝒜 = 𝒜 := by
  unfold downLeft
  ext s
  rw [Down.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨hns, hins⟩)
    · exact hs
    · by_cases hi : Sum.inl i ∈ s
      · rw [insert_eq_of_mem hi] at hins; exact absurd hins hns
      · have := h _ hins; rw [erase_insert hi] at this; exact absurd this hns
  · intro hs; exact Or.inl ⟨hs, h _ hs⟩


theorem upRight_eq_self (i : α) {𝒜 : Finset (Finset (α ⊕ α))} (h : IsUpAtRight i 𝒜) :
    upRight i 𝒜 = 𝒜 := by
  unfold upRight upComp
  ext s
  rw [UV.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨hns, b, hb, hbs⟩)
    · exact hs
    · 
      by_cases hi : Sum.inr i ∈ b
      · 
        have : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ b = b := by
          rw [UV.compress]; simp [Finset.disjoint_singleton_left, hi]
        rw [this] at hbs; rw [← hbs] at hns; exact absurd hb hns
      · 
        have hc : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ b = insert (Sum.inr i) b := by
          rw [UV.compress_of_disjoint_of_le]
          · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
          · simp [Finset.disjoint_singleton_left, hi]
          · exact bot_le
        rw [hc] at hbs; rw [← hbs] at hns; exact absurd (h _ hb) hns
  · intro hs
    refine Or.inl ⟨hs, ?_⟩
    by_cases hi : Sum.inr i ∈ s
    · have : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ s = s := by
        rw [UV.compress]; simp [Finset.disjoint_singleton_left, hi]
      rw [this]; exact hs
    · have hc : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ s = insert (Sum.inr i) s := by
        rw [UV.compress_of_disjoint_of_le]
        · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
        · simp [Finset.disjoint_singleton_left, hi]
        · exact bot_le
      rw [hc]; exact h _ hs




theorem doubleCompress_eq_self (i : α) {𝒜 : Finset (Finset (α ⊕ α))}
    (hd : IsDownAtLeft i 𝒜) (hu : IsUpAtRight i 𝒜) :
    doubleCompress i 𝒜 = 𝒜 := by
  unfold doubleCompress
  rw [downLeft_eq_self i hd, upRight_eq_self i hu]




theorem boxDoubled_card_le_mul_of_fixed (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card :=
  card_boxDoubled_le_mul 𝒜 ℬ


























































end StatMech
