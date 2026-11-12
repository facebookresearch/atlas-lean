/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Walls.rc5_itercompcard

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

variable {α : Type*} [DecidableEq α]












theorem rc6_downComp_card (i : α) (𝒜 : Finset (Finset α)) :
    #(Down.compression i 𝒜) = #𝒜 :=
  Down.card_compression i 𝒜








theorem rc6_downComp_idem (i : α) (𝒜 : Finset (Finset α)) :
    Down.compression i (Down.compression i 𝒜) = Down.compression i 𝒜 :=
  Down.compression_idem i 𝒜











theorem rc6_downComp_eq_self_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) (i : α) :
    Down.compression i 𝒜 = 𝒜 := by
  ext s
  rw [Down.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨_, hins⟩)
    · 
      exact hs
    · 
      exact h (Finset.subset_insert i s) hins
  · intro hs
    
    exact Or.inl ⟨hs, h (Finset.erase_subset _ _) hs⟩



















theorem rc6_card_member_add_nonMember (i : α) (𝒜 : Finset (Finset α)) :
    #(𝒜.memberSubfamily i) + #(𝒜.nonMemberSubfamily i) = #𝒜 :=
  card_memberSubfamily_add_card_nonMemberSubfamily i 𝒜





theorem rc6_member_union_nonMember (i : α) (𝒜 : Finset (Finset α)) :
    𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i = 𝒜.image (fun s => s.erase i) :=
  memberSubfamily_union_nonMemberSubfamily i 𝒜






theorem rc6_member_subset_nonMember_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) (i : α) :
    𝒜.memberSubfamily i ⊆ 𝒜.nonMemberSubfamily i :=
  h.memberSubfamily_subset_nonMemberSubfamily







theorem rc6_downComp_member_subset_nonMember (i : α) (𝒜 : Finset (Finset α)) :
    (Down.compression i 𝒜).memberSubfamily i ⊆ (Down.compression i 𝒜).nonMemberSubfamily i := by
  intro s hs
  rw [mem_memberSubfamily] at hs
  rw [mem_nonMemberSubfamily]
  exact ⟨Down.mem_compression_of_insert_mem_compression hs.1, hs.2⟩



















theorem rc6_event_down_compression (i : α) (𝒜 : Finset (Finset α)) :
    
    #(Down.compression i 𝒜) = #𝒜
    
    ∧ Down.compression i (Down.compression i 𝒜) = Down.compression i 𝒜
    
    ∧ (IsLowerSet (𝒜 : Set (Finset α)) → Down.compression i 𝒜 = 𝒜)
    
    ∧ #(𝒜.memberSubfamily i) + #(𝒜.nonMemberSubfamily i) = #𝒜
    ∧ 𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i = 𝒜.image (fun s => s.erase i)
    
    ∧ (IsLowerSet (𝒜 : Set (Finset α)) → 𝒜.memberSubfamily i ⊆ 𝒜.nonMemberSubfamily i)
    
    ∧ (Down.compression i 𝒜).memberSubfamily i ⊆ (Down.compression i 𝒜).nonMemberSubfamily i :=
  ⟨rc6_downComp_card i 𝒜, rc6_downComp_idem i 𝒜,
    fun h => rc6_downComp_eq_self_of_isLowerSet h i,
    rc6_card_member_add_nonMember i 𝒜, rc6_member_union_nonMember i 𝒜,
    fun h => rc6_member_subset_nonMember_of_isLowerSet h i,
    rc6_downComp_member_subset_nonMember i 𝒜⟩









theorem rc6_downComp_empty (i : α) :
    Down.compression i (∅ : Finset (Finset α)) = ∅ :=
  rc6_downComp_eq_self_of_isLowerSet (by simp [IsLowerSet]) i



theorem rc6_downComp_singleton_empty (i : α) :
    Down.compression i ({∅} : Finset (Finset α)) = {∅} := by
  refine rc6_downComp_eq_self_of_isLowerSet ?_ i
  intro s t hts hs
  simp only [coe_singleton, Set.mem_singleton_iff] at hs ⊢
  subst hs
  exact Finset.subset_empty.1 hts




theorem rc6_downComp_card_powerset (i : α) (s : Finset α) :
    #(Down.compression i s.powerset) = 2 ^ s.card := by
  rw [rc6_downComp_card, Finset.card_powerset]

end StatMech.Walls
