/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Code.Inequalities.ReimerDoubled
import Mathlib.Combinatorics.SetFamily.Compression.UV

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]










lemma uvCompress_singleton_empty (a : α) (s : Finset α) :
    UV.compress ({a} : Finset α) ∅ s = insert a s := by
  by_cases ha : a ∈ s
  · rw [UV.compress]
    simp only [Finset.disjoint_singleton_left, ha, not_true, false_and, if_false]
    rw [insert_eq_of_mem ha]
  · rw [UV.compress_of_disjoint_of_le]
    · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
    · simp [Finset.disjoint_singleton_left, ha]
    · exact bot_le



lemma mem_upComp (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) (s : Finset (α ⊕ α)) :
    s ∈ upComp a 𝒜 ↔
      (s ∈ 𝒜 ∧ insert a s ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ ∃ b ∈ 𝒜, insert a b = s) := by
  unfold upComp
  rw [UV.mem_compression]
  simp_rw [uvCompress_singleton_empty]


lemma mem_upRight (i : α) (𝒜 : Finset (Finset (α ⊕ α))) (s : Finset (α ⊕ α)) :
    s ∈ upRight i 𝒜 ↔
      (s ∈ 𝒜 ∧ insert (Sum.inr i) s ∈ 𝒜) ∨
        (s ∉ 𝒜 ∧ ∃ b ∈ 𝒜, insert (Sum.inr i) b = s) :=
  mem_upComp (Sum.inr i) 𝒜 s



lemma mem_downLeft (i : α) (𝒜 : Finset (Finset (α ⊕ α))) (s : Finset (α ⊕ α)) :
    s ∈ downLeft i 𝒜 ↔
      (s ∈ 𝒜 ∧ s.erase (Sum.inl i) ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ insert (Sum.inl i) s ∈ 𝒜) := by
  unfold downLeft
  exact Down.mem_compression


lemma insert_mem_upComp (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) {b : Finset (α ⊕ α)}
    (hb : b ∈ 𝒜) : insert a b ∈ upComp a 𝒜 := by
  have := UV.compress_mem_compression (s := 𝒜) (u := ({a} : Finset (α ⊕ α))) (v := ∅) hb
  rwa [uvCompress_singleton_empty] at this


lemma upComp_isUp (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) {s : Finset (α ⊕ α)}
    (hs : s ∈ upComp a 𝒜) : insert a s ∈ upComp a 𝒜 := by
  unfold upComp at hs ⊢
  have := UV.compress_mem_compression_of_mem_compression (s := 𝒜) (u := ({a} : Finset (α ⊕ α)))
    (v := ∅) (a := s) hs
  rwa [uvCompress_singleton_empty] at this








theorem downLeft_isDownAtLeft (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    IsDownAtLeft i (downLeft i 𝒜) := by
  intro s hs
  unfold downLeft at hs ⊢
  exact Down.erase_mem_compression_of_mem_compression hs


theorem upRight_isUpAtRight (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    IsUpAtRight i (upRight i 𝒜) := by
  intro s hs
  unfold upRight at hs ⊢
  exact upComp_isUp _ _ hs













theorem upRight_isDownAtLeft (i j : α) {𝒜 : Finset (Finset (α ⊕ α))} (h : IsDownAtLeft i 𝒜) :
    IsDownAtLeft i (upRight j 𝒜) := by
  intro s hs
  unfold upRight at hs ⊢
  have hne : (Sum.inl i : α ⊕ α) ≠ Sum.inr j := by simp
  rw [mem_upComp] at hs
  rw [mem_upComp]
  rcases hs with ⟨hsA, hins⟩ | ⟨hns, b, hbA, rfl⟩
  · 
    
    left
    refine ⟨h _ hsA, ?_⟩
    rw [← Finset.erase_insert_of_ne hne.symm]
    exact h _ hins
  · 
    
    rw [Finset.erase_insert_of_ne hne.symm]
    set c := b.erase (Sum.inl i) with hc
    have hcA : c ∈ 𝒜 := h _ hbA
    by_cases hmem : insert (Sum.inr j) c ∈ 𝒜
    · left
      exact ⟨hmem, by rw [Finset.insert_idem]; exact hmem⟩
    · right
      exact ⟨hmem, c, hcA, rfl⟩



theorem downLeft_isUpAtRight (i j : α) {𝒜 : Finset (Finset (α ⊕ α))} (h : IsUpAtRight j 𝒜) :
    IsUpAtRight j (downLeft i 𝒜) := by
  intro s hs
  unfold downLeft at hs ⊢
  have hne : (Sum.inr j : α ⊕ α) ≠ Sum.inl i := by simp
  rw [Down.mem_compression] at hs ⊢
  rcases hs with ⟨hsA, hers⟩ | ⟨hns, hins⟩
  · 
    
    left
    refine ⟨h _ hsA, ?_⟩
    rw [Finset.erase_insert_of_ne hne]
    exact h _ hers
  · 
    have hi_notin : (Sum.inl i : α ⊕ α) ∉ s :=
      fun hc => hns (by rwa [insert_eq_of_mem hc] at hins)
    by_cases hmem : insert (Sum.inr j) s ∈ 𝒜
    · 
      left
      refine ⟨hmem, ?_⟩
      rw [Finset.erase_eq_of_notMem (by simp [hi_notin])]
      exact hmem
    · 
      right
      refine ⟨hmem, ?_⟩
      rw [← Finset.insert_comm]
      exact h _ hins










theorem doubleCompress_isDownAtLeft (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    IsDownAtLeft i (doubleCompress i 𝒜) := by
  unfold doubleCompress
  exact upRight_isDownAtLeft i i (downLeft_isDownAtLeft i 𝒜)


theorem doubleCompress_isUpAtRight (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    IsUpAtRight i (doubleCompress i 𝒜) := by
  unfold doubleCompress
  exact upRight_isUpAtRight i (downLeft i 𝒜)





theorem doubleCompress_idem (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    doubleCompress i (doubleCompress i 𝒜) = doubleCompress i 𝒜 :=
  doubleCompress_eq_self i (doubleCompress_isDownAtLeft i 𝒜) (doubleCompress_isUpAtRight i 𝒜)













theorem boxDoubled_filter_notMem_inl (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).filter (fun U => Sum.inl i ∉ U)
      = boxDoubled (𝒜.filter (fun S => i ∉ S)) ℬ := by
  ext U
  simp only [mem_filter, mem_boxDoubled]
  constructor
  · rintro ⟨⟨S, hS, T, hT, hd, rfl⟩, hiU⟩
    rw [mem_dbl_inl] at hiU
    exact ⟨S, ⟨hS, hiU⟩, T, hT, hd, rfl⟩
  · rintro ⟨S, ⟨hS, hiS⟩, T, hT, hd, rfl⟩
    refine ⟨⟨S, hS, T, hT, hd, rfl⟩, ?_⟩
    rw [mem_dbl_inl]; exact hiS



theorem boxDoubled_filter_notMem_inr (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).filter (fun U => Sum.inr i ∉ U)
      = boxDoubled 𝒜 (ℬ.filter (fun T => i ∉ T)) := by
  ext U
  simp only [mem_filter, mem_boxDoubled]
  constructor
  · rintro ⟨⟨S, hS, T, hT, hd, rfl⟩, hiU⟩
    rw [mem_dbl_inr] at hiU
    exact ⟨S, hS, T, ⟨hT, hiU⟩, hd, rfl⟩
  · rintro ⟨S, hS, T, ⟨hT, hiT⟩, hd, rfl⟩
    refine ⟨⟨S, hS, T, hT, hd, rfl⟩, ?_⟩
    rw [mem_dbl_inr]; exact hiT




theorem boxDoubled_mono {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ 𝒜') (hℬ : ℬ ⊆ ℬ') :
    boxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜' ℬ' := by
  intro U hU
  rw [mem_boxDoubled] at hU ⊢
  obtain ⟨S, hS, T, hT, hd, hU⟩ := hU
  exact ⟨S, h𝒜 hS, T, hℬ hT, hd, hU⟩


theorem card_boxDoubled_mono {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ 𝒜') (hℬ : ℬ ⊆ ℬ') :
    (boxDoubled 𝒜 ℬ).card ≤ (boxDoubled 𝒜' ℬ').card :=
  Finset.card_le_card (boxDoubled_mono h𝒜 hℬ)









omit [DecidableEq α] in

theorem dbl_parts_disjoint (S T : Finset α) :
    Disjoint (S.map ⟨Sum.inl, Sum.inl_injective⟩) (T.map ⟨Sum.inr, Sum.inr_injective⟩) := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hxS hxT
  obtain ⟨a, _, rfl⟩ := hxS
  obtain ⟨b, _, hb⟩ := hxT
  exact Sum.inl_ne_inr hb.symm






























































end StatMech
