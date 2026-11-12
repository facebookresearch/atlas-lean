/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.Walls.rc64consolidation
import Code.Walls.rc41hall
import Code.Walls.rc40sdr

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}







open Classical in



theorem rc65_nbhd_nonempty (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) : (rc59_nbhd 𝒜 ℬ S).Nonempty := by
  rw [rc59_nbhd_eq_admOneSidedA]
  exact rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS

open Classical in


theorem rc65_pair_biUnion (𝒜 ℬ : Finset (Finset (Fin n))) (S₁ S₂ : Finset (Fin n)) :
    ({S₁, S₂} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)
      = rc59_nbhd 𝒜 ℬ S₁ ∪ rc59_nbhd 𝒜 ℬ S₂ := by
  rw [Finset.biUnion_insert, Finset.singleton_biUnion]



def rc65_MarriageTwoPair (𝒜 ℬ : Finset (Finset (Fin n))) (S₁ S₂ : Finset (Fin n)) : Prop :=
  2 ≤ (rc59_nbhd 𝒜 ℬ S₁ ∪ rc59_nbhd 𝒜 ℬ S₂).card



open Classical in



theorem rc65_marriage_two_of_nbhd_card_ge_two (𝒜 ℬ : Finset (Finset (Fin n)))
    (S₁ S₂ : Finset (Fin n))
    (h : 2 ≤ (rc59_nbhd 𝒜 ℬ S₁).card ∨ 2 ≤ (rc59_nbhd 𝒜 ℬ S₂).card) :
    rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  rcases h with h | h
  · exact h.trans (Finset.card_le_card Finset.subset_union_left)
  · exact h.trans (Finset.card_le_card Finset.subset_union_right)

open Classical in



theorem rc65_marriage_two_of_nbhd_ne (𝒜 ℬ : Finset (Finset (Fin n)))
    {S₁ S₂ : Finset (Fin n)}
    (h1 : (rc59_nbhd 𝒜 ℬ S₁).Nonempty) (h2 : (rc59_nbhd 𝒜 ℬ S₂).Nonempty)
    (hne : rc59_nbhd 𝒜 ℬ S₁ ≠ rc59_nbhd 𝒜 ℬ S₂) :
    rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  rw [rc65_MarriageTwoPair, show (2 : ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff,
    Finset.one_lt_card_iff]
  
  obtain ⟨x, hx⟩ : ∃ x, (x ∈ rc59_nbhd 𝒜 ℬ S₁ ∧ x ∉ rc59_nbhd 𝒜 ℬ S₂) ∨
      (x ∈ rc59_nbhd 𝒜 ℬ S₂ ∧ x ∉ rc59_nbhd 𝒜 ℬ S₁) := by
    rw [Ne, Finset.ext_iff, not_forall] at hne
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    by_cases h1 : x ∈ rc59_nbhd 𝒜 ℬ S₁
    · exact Or.inl ⟨h1, fun h2 => hx (iff_of_true h1 h2)⟩
    · have h2 : x ∈ rc59_nbhd 𝒜 ℬ S₂ := by
        by_contra h2
        exact hx (iff_of_false h1 h2)
      exact Or.inr ⟨h2, h1⟩
  rcases hx with ⟨hxS1, hxS2⟩ | ⟨hxS2, hxS1⟩
  · obtain ⟨y, hy⟩ := h2
    exact ⟨x, y, Finset.mem_union_left _ hxS1, Finset.mem_union_right _ hy,
      fun h => hxS2 (h ▸ hy)⟩
  · obtain ⟨y, hy⟩ := h1
    exact ⟨x, y, Finset.mem_union_right _ hxS2, Finset.mem_union_left _ hy,
      fun h => hxS1 (h ▸ hy)⟩

open Classical in






theorem rc65_marriage_two_of_commonWitness (𝒜 ℬ : Finset (Finset (Fin n)))
    {S₁ S₂ K : Finset (Fin n)}
    (hKA₁ : ∀ T : Finset (Fin n), T ∩ K = S₁ ∩ K → T ∈ 𝒜)
    (hKA₂ : ∀ T : Finset (Fin n), T ∩ K = S₂ ∩ K → T ∈ 𝒜)
    (hKcB₁ : ∀ T : Finset (Fin n), T ∩ Kᶜ = S₁ ∩ Kᶜ → T ∈ ℬ)
    (hKcB₂ : ∀ T : Finset (Fin n), T ∩ Kᶜ = S₂ ∩ Kᶜ → T ∈ ℬ)
    (htrace : S₁ ∩ K ≠ S₂ ∩ K) :
    rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  
  have hr₁ : rc36_R0 S₁ K Kᶜ ∈ rc59_nbhd 𝒜 ℬ S₁ := by
    rw [rc59_nbhd_eq_admOneSidedA]
    exact rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ hKA₁ hKcB₁
  have hr₂ : rc36_R0 S₂ K Kᶜ ∈ rc59_nbhd 𝒜 ℬ S₂ := by
    rw [rc59_nbhd_eq_admOneSidedA]
    exact rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ hKA₂ hKcB₂
  have hrne : rc36_R0 S₁ K Kᶜ ≠ rc36_R0 S₂ K Kᶜ := by
    intro h
    exact htrace (rc41_R0cover_traceEq S₁ S₂ K h)
  rw [rc65_MarriageTwoPair, show (2 : ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff,
    Finset.one_lt_card_iff]
  exact ⟨rc36_R0 S₁ K Kᶜ, rc36_R0 S₂ K Kᶜ, Finset.mem_union_left _ hr₁,
    Finset.mem_union_right _ hr₂, hrne⟩



open Classical in









def rc65_SingletonNbhdInjective : Prop :=
  ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)},
    S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ →
    ∀ R : Finset (Fin m), rc59_nbhd 𝒜 ℬ S₁ = {R} → rc59_nbhd 𝒜 ℬ S₂ = {R} → False



open Classical in




theorem rc65_marriage_two_of_singletonInjective (h : rc65_SingletonNbhdInjective)
    (𝒜 ℬ : Finset (Finset (Fin n))) {S₁ S₂ : Finset (Fin n)}
    (hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ) (hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ) (hne : S₁ ≠ S₂) :
    rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  classical
  by_cases hbig : 2 ≤ (rc59_nbhd 𝒜 ℬ S₁).card ∨ 2 ≤ (rc59_nbhd 𝒜 ℬ S₂).card
  · exact rc65_marriage_two_of_nbhd_card_ge_two 𝒜 ℬ S₁ S₂ hbig
  · rw [not_or, Nat.not_le, Nat.not_le] at hbig
    obtain ⟨hb1, hb2⟩ := hbig
    
    have h1ne := rc65_nbhd_nonempty 𝒜 ℬ hS₁
    have h2ne := rc65_nbhd_nonempty 𝒜 ℬ hS₂
    have hc1 : (rc59_nbhd 𝒜 ℬ S₁).card = 1 :=
      le_antisymm (Nat.lt_succ_iff.mp hb1) h1ne.card_pos
    have hc2 : (rc59_nbhd 𝒜 ℬ S₂).card = 1 :=
      le_antisymm (Nat.lt_succ_iff.mp hb2) h2ne.card_pos
    obtain ⟨R₁, hR₁⟩ := Finset.card_eq_one.mp hc1
    obtain ⟨R₂, hR₂⟩ := Finset.card_eq_one.mp hc2
    by_cases hRR : R₁ = R₂
    · subst hRR
      exact (h n 𝒜 ℬ hS₁ hS₂ hne R₁ hR₁ hR₂).elim
    · refine rc65_marriage_two_of_nbhd_ne 𝒜 ℬ h1ne h2ne ?_
      rw [hR₁, hR₂]
      simpa using hRR

open Classical in



theorem rc65_singletonInjective_of_marriageTwo
    (h : ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)},
      S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ →
      rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂) :
    rc65_SingletonNbhdInjective := by
  intro m 𝒜 ℬ S₁ S₂ hS₁ hS₂ hne R hR₁ hR₂
  have hm := h m 𝒜 ℬ hS₁ hS₂ hne
  rw [rc65_MarriageTwoPair, hR₁, hR₂, Finset.union_self, Finset.card_singleton] at hm
  omega

open Classical in



theorem rc65_marriageTwo_iff_singletonInjective :
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)},
      S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ →
      rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂)
    ↔ rc65_SingletonNbhdInjective :=
  ⟨rc65_singletonInjective_of_marriageTwo,
   fun h _m 𝒜 ℬ {_S₁ _S₂} hS₁ hS₂ hne =>
     rc65_marriage_two_of_singletonInjective h 𝒜 ℬ hS₁ hS₂ hne⟩

open Classical in



theorem rc65_marriage_subfamily_two_of_singletonInjective (h : rc65_SingletonNbhdInjective)
    (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))}
    (h𝒯 : 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ) (hcard : 𝒯.card = 2) :
    𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  obtain ⟨S₁, S₂, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  have hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ := h𝒯 (by simp)
  have hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ := h𝒯 (by simp)
  rw [hcard, rc65_pair_biUnion]
  exact rc65_marriage_two_of_singletonInjective h 𝒜 ℬ hS₁ hS₂ hne

open Classical in




theorem rc65_marriage_card_le_two_of_singletonInjective (h : rc65_SingletonNbhdInjective)
    (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))}
    (h𝒯 : 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ) (hcard : 𝒯.card ≤ 2) :
    𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  rcases Nat.lt_or_ge 𝒯.card 2 with hlt | hge
  · exact rc64_marriage_card_le_one 𝒜 ℬ 𝒯 h𝒯 (Nat.lt_succ_iff.mp hlt)
  · have hc : 𝒯.card = 2 := le_antisymm hcard hge
    exact rc65_marriage_subfamily_two_of_singletonInjective h 𝒜 ℬ h𝒯 hc











open Classical in



theorem rc65_marriageTwoPair_fin2 (𝒜 ℬ : Finset (Finset (Fin 2)))
    {S₁ S₂ : Finset (Fin 2)} (hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ) (hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
    (hne : S₁ ≠ S₂) : rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  have hsub : ({S₁, S₂} : Finset (Finset (Fin 2))) ⊆ rc20_famCylBox 𝒜 ℬ := by
    intro T hT
    rw [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl <;> assumption
  have hHall := rc59_indepHall_fin2 𝒜 ℬ ({S₁, S₂}) (Finset.mem_powerset.mpr hsub)
  rw [Finset.card_pair hne, rc65_pair_biUnion] at hHall
  exact hHall

open Classical in




theorem rc65_singletonInjective_fin2 (𝒜 ℬ : Finset (Finset (Fin 2)))
    {S₁ S₂ : Finset (Fin 2)} (hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ) (hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
    (hne : S₁ ≠ S₂) (R : Finset (Fin 2))
    (hR₁ : rc59_nbhd 𝒜 ℬ S₁ = {R}) (hR₂ : rc59_nbhd 𝒜 ℬ S₂ = {R}) : False := by
  have hm := rc65_marriageTwoPair_fin2 𝒜 ℬ hS₁ hS₂ hne
  rw [rc65_MarriageTwoPair, hR₁, hR₂, Finset.union_self, Finset.card_singleton] at hm
  omega

open Classical in





theorem rc65_marriageTwoPair_fin3_refuter
    {S₁ S₂ : Finset (Fin 3)} (hS₁ : S₁ ∈ rc20_famCylBox rc32_A3 rc32_B3)
    (hS₂ : S₂ ∈ rc20_famCylBox rc32_A3 rc32_B3) (hne : S₁ ≠ S₂) :
    rc65_MarriageTwoPair rc32_A3 rc32_B3 S₁ S₂ := by
  have hsub : ({S₁, S₂} : Finset (Finset (Fin 3))) ⊆ rc20_famCylBox rc32_A3 rc32_B3 := by
    intro T hT
    rw [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl <;> assumption
  have hHall := rc59_indepHall_fin3_refuter ({S₁, S₂}) (Finset.mem_powerset.mpr hsub)
  rw [Finset.card_pair hne, rc65_pair_biUnion] at hHall
  exact hHall











theorem rc65_refuter_box_two : rc21_boxComp 3 rc40_Aref rc40_Bref = {{0}, {1}} :=
  rc40_box_fin3





theorem rc65_refuter_R0values_collapse :
    rc40_R0valuesComp 3 rc40_Aref rc40_Bref {0} = {∅}
      ∧ rc40_R0valuesComp 3 rc40_Aref rc40_Bref {1} = {∅} :=
  ⟨rc40_R0values_empty_zero_fin3, rc40_R0values_empty_one_fin3⟩






theorem rc65_refuter_R0_insufficient_for_two :
    (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
        (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
      < (rc21_boxComp 3 rc40_Aref rc40_Bref).card :=
  rc40_R0values_biUnion_lt_box_fin3



theorem rc65_refuter_hall_holds :
    rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true :=
  rc40_hallOneSidedA_holds_fin3



open Classical in


























theorem rc65_status :
    
    ((∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)},
        S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ →
        rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂) ↔ rc65_SingletonNbhdInjective) ∧
    
    (rc65_SingletonNbhdInjective → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m)))
        (𝒯 : Finset (Finset (Fin m))),
        𝒯 ⊆ rc20_famCylBox 𝒜 ℬ → 𝒯.card ≤ 2 →
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ K : Finset (Fin m)},
        (∀ T : Finset (Fin m), T ∩ K = S₁ ∩ K → T ∈ 𝒜) →
        (∀ T : Finset (Fin m), T ∩ K = S₂ ∩ K → T ∈ 𝒜) →
        (∀ T : Finset (Fin m), T ∩ Kᶜ = S₁ ∩ Kᶜ → T ∈ ℬ) →
        (∀ T : Finset (Fin m), T ∩ Kᶜ = S₂ ∩ Kᶜ → T ∈ ℬ) →
        S₁ ∩ K ≠ S₂ ∩ K → rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂) ∧
    
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) {S₁ S₂ : Finset (Fin 2)},
        S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ →
        ∀ R : Finset (Fin 2), rc59_nbhd 𝒜 ℬ S₁ = {R} → rc59_nbhd 𝒜 ℬ S₂ = {R} → False) ∧
    
    (∀ {S₁ S₂ : Finset (Fin 3)}, S₁ ∈ rc20_famCylBox rc32_A3 rc32_B3 →
        S₂ ∈ rc20_famCylBox rc32_A3 rc32_B3 → S₁ ≠ S₂ →
        rc65_MarriageTwoPair rc32_A3 rc32_B3 S₁ S₂) ∧
    
    (rc21_boxComp 3 rc40_Aref rc40_Bref = {{0}, {1}}) ∧
    ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion
        (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card
      < (rc21_boxComp 3 rc40_Aref rc40_Bref).card) ∧
    (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true) :=
  ⟨rc65_marriageTwo_iff_singletonInjective,
   fun h _m 𝒜 ℬ _𝒯 h𝒯 hcard => rc65_marriage_card_le_two_of_singletonInjective h 𝒜 ℬ h𝒯 hcard,
   fun _m 𝒜 ℬ {_S₁ _S₂ _K} hKA₁ hKA₂ hKcB₁ hKcB₂ ht =>
     rc65_marriage_two_of_commonWitness 𝒜 ℬ hKA₁ hKA₂ hKcB₁ hKcB₂ ht,
   fun 𝒜 ℬ {_S₁ _S₂} hS₁ hS₂ hne R hR₁ hR₂ =>
     rc65_singletonInjective_fin2 𝒜 ℬ hS₁ hS₂ hne R hR₁ hR₂,
   fun {_S₁ _S₂} hS₁ hS₂ hne => rc65_marriageTwoPair_fin3_refuter hS₁ hS₂ hne,
   rc65_refuter_box_two, rc65_refuter_R0_insufficient_for_two, rc65_refuter_hall_holds⟩

end StatMech.Walls
