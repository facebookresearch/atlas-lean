/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Code.Walls.rc35hallproof

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










def rc36_R0 (S K L : Finset α) : Finset α := (S ∩ K) ∪ (L \ S)

omit [Fintype α] in



theorem rc36_R0_inter_left (S K L : Finset α) (hKL : Disjoint K L) :
    rc36_R0 S K L ∩ K = S ∩ K := by
  rw [rc36_R0]
  ext x
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨h1 | ⟨hxL, _⟩, hxK⟩
    · exact ⟨h1.1, hxK⟩
    · exact absurd hxL (Finset.disjoint_left.mp hKL hxK)
  · rintro ⟨hxS, hxK⟩
    exact ⟨Or.inl ⟨hxS, hxK⟩, hxK⟩





theorem rc36_R0_compl_inter_right (S K L : Finset α) (hKL : Disjoint K L) :
    (rc36_R0 S K L)ᶜ ∩ L = S ∩ L := by
  rw [rc36_R0]
  ext x
  simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨hxnot, hxL⟩
    refine ⟨?_, hxL⟩
    by_contra hxS
    exact hxnot (Or.inr ⟨hxL, hxS⟩)
  · rintro ⟨hxS, hxL⟩
    refine ⟨?_, hxL⟩
    rintro (⟨_, hxK⟩ | ⟨_, hxnS⟩)
    · exact Finset.disjoint_left.mp hKL hxK hxL
    · exact hxnS hxS






theorem rc36_R0_mem_reflInter (𝒜 ℬ : Finset (Finset α)) {S K L : Finset α}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    rc36_R0 S K L ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter]
  refine ⟨hKA _ (rc36_R0_inter_left S K L hKL), hLB _ ?_⟩
  exact rc36_R0_compl_inter_right S K L hKL




theorem rc36_R0_mem_traceSlice (𝒜 ℬ : Finset (Finset α)) {S K L : Finset α}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    rc36_R0 S K L ∈ rc35_traceSlice 𝒜 ℬ K S := by
  rw [rc35_traceSlice, Finset.mem_filter]
  exact ⟨rc36_R0_mem_reflInter 𝒜 ℬ hKL hKA hLB, rc36_R0_inter_left S K L hKL⟩

open Classical in






theorem rc36_R0_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S K L : Finset (Fin n)}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
    rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S :=
  rc35_slice_subset_admOneSidedA n 𝒜 ℬ hKA (rc36_R0_mem_traceSlice 𝒜 ℬ hKL hKA hLB)

open Classical in





theorem rc36_admOneSidedA_nonempty_of_mem_box (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    (rc33_admOneSidedA n 𝒜 ℬ S).Nonempty := by
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  exact ⟨rc36_R0 S K L, rc36_R0_mem_admOneSidedA n 𝒜 ℬ hKL hKA hLB⟩

open Classical in




theorem rc36_hallOneSidedA_singletons (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ({S} : Finset (Finset (Fin n))).card
      ≤ (({S} : Finset (Finset (Fin n))).biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  rw [Finset.card_singleton, Finset.singleton_biUnion]
  exact (rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS).card_pos












theorem rc36_traceClass_antitone (n : ℕ) {K K' : Finset (Fin n)} (hKK' : K ⊆ K')
    (S : Finset (Fin n)) : rc20_traceClass n K' S ⊆ rc20_traceClass n K S := by
  intro T hT
  rw [rc20_traceClass, Finset.mem_filter] at hT ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have hT' := hT.2
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hxT, hxK⟩
    have : x ∈ T ∩ K' := Finset.mem_inter.mpr ⟨hxT, hKK' hxK⟩
    rw [hT'] at this
    exact ⟨(Finset.mem_inter.mp this).1, hxK⟩
  · rintro ⟨hxS, hxK⟩
    have : x ∈ S ∩ K' := Finset.mem_inter.mpr ⟨hxS, hKK' hxK⟩
    rw [← hT'] at this
    exact ⟨(Finset.mem_inter.mp this).1, hxK⟩






theorem rc36_awitsA_upward_closed (n : ℕ) (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n))
    {K K' : Finset (Fin n)} (hK : K ∈ rc35_awitsA n 𝒜 S) (hKK' : K ⊆ K') :
    K' ∈ rc35_awitsA n 𝒜 S := by
  rw [rc35_awitsA, Finset.mem_filter] at hK ⊢
  exact ⟨Finset.mem_univ _, (rc36_traceClass_antitone n hKK' S).trans hK.2⟩























def rc36_A3ex : Finset (Finset (Fin 3)) := {∅, {1}, {2}, {0, 1}, {1, 2}, {0, 1, 2}}


def rc36_B3ex : Finset (Finset (Fin 3)) := {∅, {0}, {1}}

set_option maxRecDepth 4000 in



theorem rc36_neighbour_empty_singleton_fin3 :
    rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅ = {{1, 2}} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in



theorem rc36_neighbour_one_fin3 :
    rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1} = {{1, 2}, {0, 1, 2}} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in

theorem rc36_box_fin3 :
    rc21_boxComp 3 rc36_A3ex rc36_B3ex = {∅, {1}} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in



theorem rc36_minNeighbour_lt_box_fin3 :
    (rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅).card < (rc21_boxComp 3 rc36_A3ex rc36_B3ex).card := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxRecDepth 4000 in




theorem rc36_neighbour_empty_ssubset_one_fin3 :
    rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅ ⊂ rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1} := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in






theorem rc36_hallOneSidedA_holds_fin3 :
    rc33_hallOneSidedA 3 rc36_A3ex rc36_B3ex = true := by
  rw [rc36_A3ex, rc36_B3ex]; decide



set_option linter.unusedVariables false in
open Classical in


































theorem rc36_reimer_defectcounting :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S K L : Finset (Fin n)},
        Disjoint K L → (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) →
        rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)},
          S ∈ rc20_famCylBox 𝒜 ℬ → (rc33_admOneSidedA n 𝒜 ℬ S).Nonempty)
      ∧ (∀ (n : ℕ) (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n))
          {K K' : Finset (Fin n)}, K ∈ rc35_awitsA n 𝒜 S → K ⊆ K' → K' ∈ rc35_awitsA n 𝒜 S)
      ∧ (rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅
          ⊂ rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1})
      ∧ ((rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅).card
          < (rc21_boxComp 3 rc36_A3ex rc36_B3ex).card)
      ∧ (rc33_hallOneSidedA 3 rc36_A3ex rc36_B3ex = true) :=
  ⟨fun n 𝒜 ℬ _ _ _ hKL hKA hLB => rc36_R0_mem_admOneSidedA n 𝒜 ℬ hKL hKA hLB,
    fun n 𝒜 ℬ _ hS => rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS,
    fun n 𝒜 S _ _ hK hKK' => rc36_awitsA_upward_closed n 𝒜 S hK hKK',
    rc36_neighbour_empty_ssubset_one_fin3,
    rc36_minNeighbour_lt_box_fin3,
    rc36_hallOneSidedA_holds_fin3⟩

end StatMech.Walls
