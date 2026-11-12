/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Code.Inequalities.ReimerDoubled2
import Mathlib.Data.Finset.Prod

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]










def dpairsCount (𝒜 ℬ : Finset (Finset α)) : ℕ :=
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card


theorem card_boxDoubled_eq_dpairsCount (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
  rw [card_boxDoubled]; rfl


















theorem dpairsCount_filter_notMem_notMem (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∉ p.1 ∧ i ∉ p.2)).card
      = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
  unfold dpairsCount
  apply Finset.card_nbij' (fun p => p) (fun p => p)
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product, mem_nonMemberSubfamily] at hp ⊢
    obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
    exact ⟨⟨⟨hS, hi1⟩, hT, hi2⟩, hd⟩
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product, mem_nonMemberSubfamily] at hp ⊢
    obtain ⟨⟨⟨hS, hi1⟩, hT, hi2⟩, hd⟩ := hp
    exact ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩
  · intro p _; rfl
  · intro p _; rfl




theorem dpairsCount_filter_mem_fst (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1)).card
      = dpairsCount (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) := by
  
  have hrw : ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1)
           = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter
               (fun p => i ∈ p.1 ∧ i ∉ p.2) := by
    apply Finset.filter_congr
    rintro ⟨S, T⟩ hp
    rw [mem_filter] at hp
    simp only [iff_self_and]
    intro hi1 hi2
    exact (Finset.disjoint_left.mp hp.2 hi1) hi2
  rw [hrw]
  unfold dpairsCount
  apply Finset.card_nbij' (fun p => (p.1.erase i, p.2)) (fun p => (insert i p.1, p.2))
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_memberSubfamily, insert_erase hi1]; exact ⟨hS, notMem_erase _ _⟩
    · rw [mem_nonMemberSubfamily]; exact ⟨hT, hi2⟩
    · exact hd.mono_left (erase_subset _ _)
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨hS, hT⟩, hd⟩ := hp
    rw [mem_memberSubfamily] at hS
    rw [mem_nonMemberSubfamily] at hT
    obtain ⟨hSins, hiS⟩ := hS
    obtain ⟨hTm, hiT⟩ := hT
    refine ⟨⟨⟨hSins, hTm⟩, ?_⟩, ?_, ?_⟩
    · rw [Finset.disjoint_insert_left]; exact ⟨hiT, hd⟩
    · exact mem_insert_self _ _
    · exact hiT
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp
    obtain ⟨_, hi1, _⟩ := hp
    simp only [insert_erase hi1]
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp
    obtain ⟨⟨hS, _⟩, _⟩ := hp
    rw [mem_memberSubfamily] at hS
    simp only [erase_insert hS.2]




theorem dpairsCount_filter_notMem_mem (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∉ p.1 ∧ i ∈ p.2)).card
      = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
  unfold dpairsCount
  apply Finset.card_nbij' (fun p => (p.1, p.2.erase i)) (fun p => (p.1, insert i p.2))
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_nonMemberSubfamily]; exact ⟨hS, hi1⟩
    · rw [mem_memberSubfamily, insert_erase hi2]; exact ⟨hT, notMem_erase _ _⟩
    · exact hd.mono_right (erase_subset _ _)
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨hS, hT⟩, hd⟩ := hp
    rw [mem_nonMemberSubfamily] at hS
    rw [mem_memberSubfamily] at hT
    obtain ⟨hSm, hiS⟩ := hS
    obtain ⟨hTins, hiT⟩ := hT
    refine ⟨⟨⟨hSm, hTins⟩, ?_⟩, ?_, ?_⟩
    · rw [Finset.disjoint_insert_right]; exact ⟨hiS, hd⟩
    · exact hiS
    · exact mem_insert_self _ _
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp
    obtain ⟨_, _, hi2⟩ := hp
    simp only [insert_erase hi2]
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_coe, mem_filter, mem_product] at hp
    obtain ⟨⟨_, hT⟩, _⟩ := hp
    rw [mem_memberSubfamily] at hT
    simp only [erase_insert hT.2]


theorem dpairsCount_filter_mem_mem_eq_empty (𝒜 ℬ : Finset (Finset α)) (i : α) :
    ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1 ∧ i ∈ p.2) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  rintro p hp ⟨hi1, hi2⟩
  rw [mem_filter] at hp
  exact (Finset.disjoint_left.mp hp.2 hi1) hi2



















theorem dpairsCount_fiber_recursion (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ
      = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
      + dpairsCount (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
      + dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
  set D := (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2) with hD
  have hsplit1 : (D.filter (fun p => i ∈ p.1)).card
                + (D.filter (fun p => i ∉ p.1)).card = D.card :=
    Finset.card_filter_add_card_filter_not _
  have hsplit2 : ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2)).card
                + ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2)).card
              = (D.filter (fun p => i ∉ p.1)).card :=
    Finset.card_filter_add_card_filter_not _
  have e1 : (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2)
          = D.filter (fun p => i ∉ p.1 ∧ i ∈ p.2) := by rw [Finset.filter_filter]
  have e2 : (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2)
          = D.filter (fun p => i ∉ p.1 ∧ i ∉ p.2) := by rw [Finset.filter_filter]
  show D.card = _
  rw [← hsplit1, ← hsplit2, e1, e2]
  rw [dpairsCount_filter_mem_fst, ← dpairsCount_filter_notMem_mem,
    ← dpairsCount_filter_notMem_notMem]
  ring




theorem card_boxDoubled_fiber_recursion (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (boxDoubled 𝒜 ℬ).card
      = (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)).card
      + (boxDoubled (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)).card
      + (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)).card := by
  rw [card_boxDoubled_eq_dpairsCount, card_boxDoubled_eq_dpairsCount,
    card_boxDoubled_eq_dpairsCount, card_boxDoubled_eq_dpairsCount]
  exact dpairsCount_fiber_recursion 𝒜 ℬ i










theorem card_family_fiber_split (𝒜 : Finset (Finset α)) (i : α) :
    (𝒜.memberSubfamily i).card + (𝒜.nonMemberSubfamily i).card = 𝒜.card :=
  Finset.card_memberSubfamily_add_card_nonMemberSubfamily i 𝒜


































theorem reimer_butterfly_compress_step (𝒜 ℬ : Finset (Finset α)) (i : α) :
    
    (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card
    
    ∧ IsDownAtLeft i (doubleCompress i (boxDoubled 𝒜 ℬ))
    ∧ IsUpAtRight i (doubleCompress i (boxDoubled 𝒜 ℬ))
    
    ∧ (boxDoubled 𝒜 ℬ).card
        = (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)).card
        + (boxDoubled (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)).card
        + (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)).card
    
    ∧ (𝒜.memberSubfamily i).card + (𝒜.nonMemberSubfamily i).card = 𝒜.card
    ∧ (ℬ.memberSubfamily i).card + (ℬ.nonMemberSubfamily i).card = ℬ.card := by
  refine ⟨doubleCompress_card i _, doubleCompress_isDownAtLeft i _,
    doubleCompress_isUpAtRight i _, card_boxDoubled_fiber_recursion 𝒜 ℬ i,
    card_family_fiber_split 𝒜 i, card_family_fiber_split ℬ i⟩











theorem memberSubfamily_eq_empty_of_notMem (𝒜 : Finset (Finset α)) (i : α)
    (h : ∀ s ∈ 𝒜, i ∉ s) : 𝒜.memberSubfamily i = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [mem_memberSubfamily] at hs
  exact (h _ hs.1) (mem_insert_self i s)



theorem dpairsCount_fiber_recursion_of_notMem (𝒜 ℬ : Finset (Finset α)) (i : α)
    (h𝒜 : ∀ s ∈ 𝒜, i ∉ s) (hℬ : ∀ t ∈ ℬ, i ∉ t) :
    dpairsCount 𝒜 ℬ
      = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
  rw [dpairsCount_fiber_recursion 𝒜 ℬ i, memberSubfamily_eq_empty_of_notMem 𝒜 i h𝒜,
    memberSubfamily_eq_empty_of_notMem ℬ i hℬ]
  unfold dpairsCount
  simp






theorem dpairsCount_le_mul (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ ≤ 𝒜.card * ℬ.card := by
  unfold dpairsCount
  calc ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card
      ≤ (𝒜 ×ˢ ℬ).card := card_filter_le _ _
    _ = 𝒜.card * ℬ.card := card_product _ _



















































end StatMech
