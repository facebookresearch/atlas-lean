/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Walls.rc36hallmarriage
import Code.Walls.rc37doubledhall

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








omit [Fintype α] in




theorem rc40_L_sdiff_R0 (S K L : Finset α) (hKL : Disjoint K L) :
    L \ rc36_R0 S K L = S ∩ L := by
  rw [rc36_R0]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, not_or]
  constructor
  · rintro ⟨hxL, hnot⟩
    refine ⟨?_, hxL⟩
    by_contra hxS
    exact hnot.2 ⟨hxL, hxS⟩
  · rintro ⟨hxS, hxL⟩
    refine ⟨hxL, ?_, ?_⟩
    · rintro ⟨_, hxK⟩; exact Finset.disjoint_right.mp hKL hxL hxK
    · rintro ⟨_, hxnS⟩; exact hxnS hxS

omit [Fintype α] in




theorem rc40_R0_recovers_covered (S K L : Finset α) (hKL : Disjoint K L) :
    (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S ∩ (K ∪ L) := by
  rw [rc36_R0_inter_left S K L hKL, rc40_L_sdiff_R0 S K L hKL, Finset.inter_union_distrib_left]




theorem rc40_R0_recovers_of_cover (S K L : Finset α) (hKL : Disjoint K L) (hcov : K ∪ L = univ) :
    (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S := by
  rw [rc40_R0_recovers_covered S K L hKL, hcov, Finset.inter_univ]






theorem rc40_R0_injOn_of_cover (K L : Finset α) (hKL : Disjoint K L) (hcov : K ∪ L = univ)
    {S S' : Finset α} (h : rc36_R0 S K L = rc36_R0 S' K L) : S = S' := by
  have hS := rc40_R0_recovers_of_cover S K L hKL hcov
  have hS' := rc40_R0_recovers_of_cover S' K L hKL hcov
  rw [← hS, ← hS', h]














theorem rc40_coveringPair_of_mem_box (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧
      (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) := by
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  obtain ⟨_, K, L₀, hKL₀, hKA, hL₀B⟩ := hS
  refine ⟨K, Kᶜ, disjoint_compl_right, ?_, hKA, ?_⟩
  · rw [Finset.union_compl]
  · 
    have hL₀sub : L₀ ⊆ Kᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      exact Finset.disjoint_right.mp hKL₀ hx
    have hL₀wit : L₀ ∈ rc35_awitsA n ℬ S := by
      rw [rc35_awitsA, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (rc20_traceClass_subset_iff n L₀ S ℬ).mpr hL₀B⟩
    have hKcwit : Kᶜ ∈ rc35_awitsA n ℬ S :=
      rc36_awitsA_upward_closed n ℬ S hL₀wit hL₀sub
    rw [rc35_awitsA, Finset.mem_filter] at hKcwit
    exact (rc20_traceClass_subset_iff n Kᶜ S ℬ).mp hKcwit.2






theorem rc40_R0_cover_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧
      rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S ∧
      (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S := by
  obtain ⟨K, L, hKL, hcov, hKA, hLB⟩ := rc40_coveringPair_of_mem_box n 𝒜 ℬ hS
  exact ⟨K, L, hKL, hcov, rc36_R0_mem_admOneSidedA n 𝒜 ℬ hKL hKA hLB,
    rc40_R0_recovers_of_cover S K L hKL hcov⟩












def rc40_R0valuesComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ.filter (fun KL : Finset (Fin n) × Finset (Fin n) =>
      decide (Disjoint KL.1 KL.2 ∧ rc20_traceClass n KL.1 S ⊆ 𝒜 ∧
        rc20_traceClass n KL.2 S ⊆ ℬ) = true)).image
    (fun KL => rc36_R0 S KL.1 KL.2)





theorem rc40_R0values_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) :
    rc40_R0valuesComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc40_R0valuesComp, Finset.mem_image] at hR
  obtain ⟨KL, hKL, rfl⟩ := hR
  rw [Finset.mem_filter, decide_eq_true_eq] at hKL
  obtain ⟨_, hdis, hKA, hLB⟩ := hKL
  exact rc36_R0_mem_admOneSidedA n 𝒜 ℬ hdis
    ((rc20_traceClass_subset_iff n KL.1 S 𝒜).mp hKA)
    ((rc20_traceClass_subset_iff n KL.2 S ℬ).mp hLB)


def rc40_Aref : Finset (Finset (Fin 3)) := {∅, {0}, {1}}


def rc40_Bref : Finset (Finset (Fin 3)) := {{0}, {0, 1}, {0, 1, 2}, {0, 2}, {1}, {1, 2}}

set_option maxRecDepth 4000 in


theorem rc40_box_fin3 : rc21_boxComp 3 rc40_Aref rc40_Bref = {{0}, {1}} := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxRecDepth 4000 in


theorem rc40_R0values_empty_zero_fin3 :
    rc40_R0valuesComp 3 rc40_Aref rc40_Bref {0} = {∅} := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxRecDepth 4000 in



theorem rc40_R0values_empty_one_fin3 :
    rc40_R0valuesComp 3 rc40_Aref rc40_Bref {1} = {∅} := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxRecDepth 4000 in





theorem rc40_R0values_biUnion_lt_box_fin3 :
    (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
        (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
      < (rc21_boxComp 3 rc40_Aref rc40_Bref).card := by
  rw [rc40_Aref, rc40_Bref]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in







theorem rc40_hallOneSidedA_holds_fin3 :
    rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true := by
  rw [rc40_Aref, rc40_Bref]; decide











open Classical in





theorem rc40_reimer_closes_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc18_CylBoxReflInter :=
  rc35_reimer_closes_of_oneSidedInjection h



set_option linter.unusedVariables false in
open Classical in




































theorem rc40_reimer_r0insufficient :
    (∀ (S K L : Finset (Fin 3)), Disjoint K L → K ∪ L = univ →
        (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S)
      ∧ (∀ (K L : Finset (Fin 3)), Disjoint K L → K ∪ L = univ →
          ∀ {S S' : Finset (Fin 3)}, rc36_R0 S K L = rc36_R0 S' K L → S = S')
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)},
          S ∈ rc20_famCylBox 𝒜 ℬ →
          ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧
            (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
            (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
          rc40_R0valuesComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
            (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
          < (rc21_boxComp 3 rc40_Aref rc40_Bref).card)
      ∧ (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true)
      ∧ (rc35_OneSidedInjection → rc18_CylBoxReflInter) :=
  ⟨fun S K L hKL hcov => rc40_R0_recovers_of_cover S K L hKL hcov,
    fun K L hKL hcov _ _ h => rc40_R0_injOn_of_cover K L hKL hcov h,
    fun n 𝒜 ℬ _ hS => rc40_coveringPair_of_mem_box n 𝒜 ℬ hS,
    fun n 𝒜 ℬ S => rc40_R0values_subset_admOneSidedA n 𝒜 ℬ S,
    rc40_R0values_biUnion_lt_box_fin3,
    rc40_hallOneSidedA_holds_fin3,
    rc40_reimer_closes_of_oneSidedInjection⟩

end StatMech.Walls
