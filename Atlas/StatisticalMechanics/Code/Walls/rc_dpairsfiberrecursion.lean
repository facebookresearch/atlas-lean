/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Code.Inequalities.ReimerButterflyStep

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]










theorem rc_notMem_of_mem_nonMemberSubfamily (A : Finset (Finset α)) (i : α) {s : Finset α}
    (hs : s ∈ A.nonMemberSubfamily i) : i ∉ s :=
  (Finset.mem_nonMemberSubfamily.mp hs).2



theorem rc_notMem_of_mem_memberSubfamily (A : Finset (Finset α)) (i : α) {s : Finset α}
    (hs : s ∈ A.memberSubfamily i) : i ∉ s :=
  (Finset.mem_memberSubfamily.mp hs).2






theorem rc_subfamilies_drop_coordinate (A B : Finset (Finset α)) (i : α) :
    (∀ s ∈ A.nonMemberSubfamily i, i ∉ s) ∧ (∀ s ∈ A.memberSubfamily i, i ∉ s)
    ∧ (∀ t ∈ B.nonMemberSubfamily i, i ∉ t) ∧ (∀ t ∈ B.memberSubfamily i, i ∉ t) :=
  ⟨fun _ hs => rc_notMem_of_mem_nonMemberSubfamily A i hs,
   fun _ hs => rc_notMem_of_mem_memberSubfamily A i hs,
   fun _ ht => rc_notMem_of_mem_nonMemberSubfamily B i ht,
   fun _ ht => rc_notMem_of_mem_memberSubfamily B i ht⟩









theorem rc_fourthFiber_empty (A B : Finset (Finset α)) (i : α) :
    ((A ×ˢ B).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1 ∧ i ∈ p.2) = ∅ :=
  dpairsCount_filter_mem_mem_eq_empty A B i























theorem rc_dpairsCount_fiber_recursion (A B : Finset (Finset α)) (i : α) :
    dpairsCount A B
      = dpairsCount (A.nonMemberSubfamily i) (B.nonMemberSubfamily i)
      + dpairsCount (A.memberSubfamily i) (B.nonMemberSubfamily i)
      + dpairsCount (A.nonMemberSubfamily i) (B.memberSubfamily i) := by
  classical
  
  set D := (A ×ˢ B).filter (fun p => Disjoint p.1 p.2) with hD
  
  have hsS : (D.filter (fun p => i ∈ p.1)).card + (D.filter (fun p => i ∉ p.1)).card = D.card :=
    Finset.card_filter_add_card_filter_not _
  have hsSS : ((D.filter (fun p => i ∈ p.1)).filter (fun p => i ∈ p.2)).card
            + ((D.filter (fun p => i ∈ p.1)).filter (fun p => i ∉ p.2)).card
            = (D.filter (fun p => i ∈ p.1)).card :=
    Finset.card_filter_add_card_filter_not _
  have hsT : ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2)).card
           + ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2)).card
           = (D.filter (fun p => i ∉ p.1)).card :=
    Finset.card_filter_add_card_filter_not _
  
  have hempty : ((D.filter (fun p => i ∈ p.1)).filter (fun p => i ∈ p.2)).card = 0 := by
    rw [Finset.filter_filter, hD, rc_fourthFiber_empty]; rfl
  
  have eSn : ((D.filter (fun p => i ∈ p.1)).filter (fun p => i ∉ p.2)).card
           = dpairsCount (A.memberSubfamily i) (B.nonMemberSubfamily i) := by
    rw [hD, Finset.filter_filter]
    rw [Finset.filter_congr (q := fun p : Finset α × Finset α => i ∈ p.1) ?_]
    · exact dpairsCount_filter_mem_fst A B i
    · rintro ⟨S, T⟩ hp
      rw [mem_filter] at hp
      exact ⟨fun h => h.1, fun hiS => ⟨hiS, fun hiT => (Finset.disjoint_left.mp hp.2 hiS) hiT⟩⟩
  
  have eT : ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2)).card
          = dpairsCount (A.nonMemberSubfamily i) (B.memberSubfamily i) := by
    rw [Finset.filter_filter, hD]; exact dpairsCount_filter_notMem_mem A B i
  
  have eN : ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2)).card
          = dpairsCount (A.nonMemberSubfamily i) (B.nonMemberSubfamily i) := by
    rw [Finset.filter_filter, hD]; exact dpairsCount_filter_notMem_notMem A B i
  
  show D.card = _
  have key : D.card =
      ((D.filter (fun p => i ∈ p.1)).filter (fun p => i ∉ p.2)).card
      + ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2)).card
      + ((D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2)).card := by omega
  rw [key, eSn, eT, eN]; ring











theorem rc_card_boxDoubled_fiber_recursion (A B : Finset (Finset α)) (i : α) :
    (boxDoubled A B).card
      = (boxDoubled (A.nonMemberSubfamily i) (B.nonMemberSubfamily i)).card
      + (boxDoubled (A.memberSubfamily i) (B.nonMemberSubfamily i)).card
      + (boxDoubled (A.nonMemberSubfamily i) (B.memberSubfamily i)).card := by
  rw [card_boxDoubled_eq_dpairsCount, card_boxDoubled_eq_dpairsCount,
    card_boxDoubled_eq_dpairsCount, card_boxDoubled_eq_dpairsCount]
  exact rc_dpairsCount_fiber_recursion A B i

end StatMech.Walls
