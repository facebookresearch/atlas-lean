/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Code.Walls.rc41hall
import Code.Walls.rc37doubledhall

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








theorem rc42_traceSlice_disjoint_of_ne (𝒜 ℬ : Finset (Finset α)) (K S S' : Finset α)
    (h : S ∩ K ≠ S' ∩ K) :
    Disjoint (rc35_traceSlice 𝒜 ℬ K S) (rc35_traceSlice 𝒜 ℬ K S') := by
  rw [Finset.disjoint_left]
  intro R hR hR'
  rw [rc35_traceSlice, Finset.mem_filter] at hR hR'
  exact h (hR.2.symm.trans hR'.2)













def rc42_cwits (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun K => rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n Kᶜ S ⊆ ℬ)


theorem rc42_cwits_subset_awitsA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc42_cwits n 𝒜 ℬ S ⊆ rc35_awitsA n 𝒜 S := by
  intro K hK
  rw [rc42_cwits, Finset.mem_filter] at hK
  rw [rc35_awitsA, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hK.2.1⟩

open Classical in



noncomputable def rc42_admCovering (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc42_cwits n 𝒜 ℬ S).biUnion (fun K => rc35_traceSlice 𝒜 ℬ K S)

open Classical in





theorem rc42_admCovering_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc42_admCovering n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc42_admCovering, Finset.mem_biUnion] at hR
  obtain ⟨K, hK, hRslice⟩ := hR
  rw [rc42_cwits, Finset.mem_filter] at hK
  exact rc35_slice_subset_admOneSidedA n 𝒜 ℬ
    ((rc20_traceClass_subset_iff n K S 𝒜).mp hK.2.1) hRslice

open Classical in





theorem rc42_admCovering_nonempty_of_mem_box (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    (rc42_admCovering n 𝒜 ℬ S).Nonempty := by
  obtain ⟨K, L, hKL, hcov, hKA, hLB⟩ := rc40_coveringPair_of_mem_box n 𝒜 ℬ hS
  
  have hLKc : L = Kᶜ := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_compl]
      exact Finset.disjoint_right.mp hKL hx
    · intro x hx
      rw [Finset.mem_compl] at hx
      have : x ∈ K ∪ L := hcov ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp this with h | h
      · exact absurd h hx
      · exact h
  have hKcw : K ∈ rc42_cwits n 𝒜 ℬ S := by
    rw [rc42_cwits, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, ?_⟩
    rw [← hLKc]
    exact (rc20_traceClass_subset_iff n L S ℬ).mpr hLB
  refine ⟨rc36_R0 S K L, ?_⟩
  rw [rc42_admCovering, Finset.mem_biUnion]
  exact ⟨K, hKcw, rc36_R0_mem_traceSlice 𝒜 ℬ hKL hKA hLB⟩






def rc42_HallCovering : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card

open Classical in



theorem rc42_biUnionCovering_le_biUnion (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) :
    (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card
      ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  refine Finset.card_le_card (Finset.biUnion_subset.mpr ?_)
  intro S hS
  exact (rc42_admCovering_subset_admOneSidedA n 𝒜 ℬ S).trans
    (Finset.subset_biUnion_of_mem (rc33_admOneSidedA n 𝒜 ℬ) hS)

open Classical in






theorem rc42_defectZero_of_hallCovering (h : rc42_HallCovering) : rc41_DefectZero := by
  intro n 𝒜 ℬ 𝒯 h𝒯
  exact (h n 𝒜 ℬ 𝒯 h𝒯).trans (rc42_biUnionCovering_le_biUnion n 𝒜 ℬ 𝒯)

open Classical in




theorem rc42_reimer_closes_of_hallCovering (h : rc42_HallCovering) : rc18_CylBoxReflInter :=
  rc41_reimer_closes_of_defectZero (rc42_defectZero_of_hallCovering h)









open Classical in



theorem rc42_slice_subset_admCovering (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKw : ∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n Kᶜ S ⊆ ℬ)
    {S : Finset (Fin n)} (hS : S ∈ 𝒯) :
    rc35_traceSlice 𝒜 ℬ K S ⊆ rc42_admCovering n 𝒜 ℬ S := by
  intro R hR
  rw [rc42_admCovering, Finset.mem_biUnion]
  exact ⟨K, by rw [rc42_cwits, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hKw S hS⟩, hR⟩

open Classical in














theorem rc42_traceImage_le_biUnionCovering (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKw : ∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n Kᶜ S ⊆ ℬ) :
    (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  
  have himg : 𝒯.image (fun S => S ∩ K)
      = (𝒯.image (fun S => rc36_R0 S K Kᶜ)).image (fun R => R ∩ K) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro S _
    simp only [Function.comp]
    exact (rc41_R0cover_inter S K).symm
  calc (𝒯.image (fun S => S ∩ K)).card
      = ((𝒯.image (fun S => rc36_R0 S K Kᶜ)).image (fun R => R ∩ K)).card := by rw [himg]
    _ ≤ (𝒯.image (fun S => rc36_R0 S K Kᶜ)).card := Finset.card_image_le
    _ ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
        refine Finset.card_le_card ?_
        intro R hR
        rw [Finset.mem_image] at hR
        obtain ⟨S, hS, rfl⟩ := hR
        refine Finset.mem_biUnion.mpr ⟨S, hS, ?_⟩
        
        refine rc42_slice_subset_admCovering n 𝒜 ℬ hKw hS ?_
        exact rc36_R0_mem_traceSlice 𝒜 ℬ disjoint_compl_right
          ((rc20_traceClass_subset_iff n K S 𝒜).mp (hKw S hS).1)
          ((rc20_traceClass_subset_iff n Kᶜ S ℬ).mp (hKw S hS).2)

open Classical in













theorem rc42_card_biUnion_traceSlice_eq_sum (𝒜 ℬ : Finset (Finset α)) (K : Finset α)
    (𝒯 : Finset (Finset α)) :
    ((𝒯.image (fun S => S ∩ K)).biUnion (fun t => rc35_traceSlice 𝒜 ℬ K t)).card
      = ∑ t ∈ 𝒯.image (fun S => S ∩ K), (rc35_traceSlice 𝒜 ℬ K t).card := by
  refine Finset.card_biUnion ?_
  intro t ht t' ht' hne
  
  rw [Finset.mem_coe, Finset.mem_image] at ht ht'
  obtain ⟨S, _, rfl⟩ := ht
  obtain ⟨S', _, rfl⟩ := ht'
  refine rc42_traceSlice_disjoint_of_ne 𝒜 ℬ K (S ∩ K) (S' ∩ K) ?_
  
  rw [Finset.inter_assoc, Finset.inter_self, Finset.inter_assoc, Finset.inter_self]
  exact hne









def rc42_traceSliceComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (K S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc20_reflInterComp n 𝒜 ℬ).filter (fun R => R ∩ K = S ∩ K)


def rc42_admCoveringComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc42_cwits n 𝒜 ℬ S).biUnion (fun K => rc42_traceSliceComp n 𝒜 ℬ K S)

open Classical in

theorem rc42_traceSliceComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (K S : Finset (Fin n)) :
    rc42_traceSliceComp n 𝒜 ℬ K S = rc35_traceSlice 𝒜 ℬ K S := by
  rw [rc42_traceSliceComp, rc35_traceSlice, rc20_reflInterComp_eq]

open Classical in

theorem rc42_admCoveringComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc42_admCoveringComp n 𝒜 ℬ S = rc42_admCovering n 𝒜 ℬ S := by
  rw [rc42_admCoveringComp, rc42_admCovering]
  apply Finset.biUnion_congr rfl
  intro K _
  exact rc42_traceSliceComp_eq n 𝒜 ℬ K S



def rc42_hallCovering (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ 𝒯 ∈ (rc21_boxComp n 𝒜 ℬ).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc42_admCoveringComp n 𝒜 ℬ)).card)

open Classical in



theorem rc42_hallCovering_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc42_hallCovering n 𝒜 ℬ = true) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  rw [rc42_hallCovering, decide_eq_true_eq, rc21_boxComp_eq] at h
  intro 𝒯 h𝒯
  have := h 𝒯 h𝒯
  rwa [show 𝒯.biUnion (rc42_admCoveringComp n 𝒜 ℬ) = 𝒯.biUnion (rc42_admCovering n 𝒜 ℬ) from
    Finset.biUnion_congr rfl (fun S _ => rc42_admCoveringComp_eq n 𝒜 ℬ S)] at this













set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in






theorem rc42_hallCovering_holds_fin3 :
    rc42_hallCovering 3 rc40_Aref rc40_Bref = true := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in





theorem rc42_hallCovering_holds_A3ex :
    rc42_hallCovering 3 rc36_A3ex rc36_B3ex = true := by
  rw [rc36_A3ex, rc36_B3ex]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 6000 in







theorem rc42_admCovering_proper_fin3 :
    rc42_admCoveringComp 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅
      ⊂ rc33_admOneSidedA 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅ := by
  decide








theorem rc42_R0_insufficient_fin3 :
    (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
        (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
      < (rc21_boxComp 3 rc40_Aref rc40_Bref).card :=
  rc40_R0values_biUnion_lt_box_fin3



set_option linter.unusedVariables false in
open Classical in




































theorem rc42_reimer_coveringwitness :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (K S S' : Finset (Fin 3)), S ∩ K ≠ S' ∩ K →
        Disjoint (rc35_traceSlice 𝒜 ℬ K S) (rc35_traceSlice 𝒜 ℬ K S'))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
          rc42_admCovering n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (rc42_HallCovering → rc41_DefectZero)
      ∧ (rc42_HallCovering → rc18_CylBoxReflInter)
      ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true)
      ∧ ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
            (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
          < (rc21_boxComp 3 rc40_Aref rc40_Bref).card)
      ∧ (rc42_admCoveringComp 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅
          ⊂ rc33_admOneSidedA 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅) :=
  ⟨fun 𝒜 ℬ K S S' h => rc42_traceSlice_disjoint_of_ne 𝒜 ℬ K S S' h,
    fun n 𝒜 ℬ S => rc42_admCovering_subset_admOneSidedA n 𝒜 ℬ S,
    rc42_defectZero_of_hallCovering,
    rc42_reimer_closes_of_hallCovering,
    rc42_hallCovering_holds_fin3,
    rc42_R0_insufficient_fin3,
    rc42_admCovering_proper_fin3⟩

end StatMech.Walls
