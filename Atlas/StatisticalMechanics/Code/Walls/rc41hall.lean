/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Code.Walls.rc40sdr
import Code.Walls.rc36hallmarriage

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]













theorem rc41_R0cover_inter (S K : Finset α) : rc36_R0 S K Kᶜ ∩ K = S ∩ K :=
  rc36_R0_inter_left S K Kᶜ disjoint_compl_right





theorem rc41_R0cover_traceEq (S S' K : Finset α) (h : rc36_R0 S K Kᶜ = rc36_R0 S' K Kᶜ) :
    S ∩ K = S' ∩ K := by
  have := congrArg (· ∩ K) h
  simpa only [rc41_R0cover_inter] using this





theorem rc41_R0cover_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K : Finset (Fin n)} (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    rc36_R0 S K Kᶜ ∈ rc33_admOneSidedA n 𝒜 ℬ S :=
  rc36_R0_mem_admOneSidedA n 𝒜 ℬ disjoint_compl_right hKA hKcB










open Classical in









theorem rc41_hall_of_commonWitness_distinctTrace (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ)
    (hinj : Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n)))) :
    𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  refine Finset.card_le_card_of_injOn (fun S => rc36_R0 S K Kᶜ) ?_ ?_
  · 
    intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨S, hS, rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ (hKA S hS) (hKcB S hS)⟩
  · 
    intro S hS S' hS' h
    exact hinj hS hS' (rc41_R0cover_traceEq S S' K h)














open Classical in








theorem rc41_traceImage_le_biUnion (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  
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
    _ ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
        refine Finset.card_le_card ?_
        intro R hR
        rw [Finset.mem_image] at hR
        obtain ⟨S, hS, rfl⟩ := hR
        exact Finset.mem_biUnion.mpr
          ⟨S, hS, rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ (hKA S hS) (hKcB S hS)⟩













def rc41_DefectZero : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card




theorem rc41_hallOneSidedA_iff_defectZero : rc33_HallOneSidedA ↔ rc41_DefectZero := Iff.rfl

open Classical in





theorem rc41_reimer_closes_of_defectZero (h : rc41_DefectZero) : rc18_CylBoxReflInter :=
  rc33_reimer_closes_of_hallOneSidedA (rc41_hallOneSidedA_iff_defectZero.mpr h)

open Classical in




theorem rc41_reimer_closes_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc18_CylBoxReflInter :=
  rc40_reimer_closes_of_oneSidedInjection h















def rc41_hasCommonCoveringWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) : Bool :=
  decide (∃ K : Finset (Fin n),
    (∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜) ∧
    (∀ S ∈ 𝒯, rc20_traceClass n Kᶜ S ⊆ ℬ) ∧
    Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n))))

set_option maxRecDepth 4000 in






theorem rc41_commonWitness_collidingTrace_fin3 :
    rc41_hasCommonCoveringWitness 3 rc40_Aref rc40_Bref {{0}, {1}} = false := by
  rw [rc40_Aref, rc40_Bref, rc41_hasCommonCoveringWitness]; decide






theorem rc41_hallOneSidedA_holds_fin3 :
    rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true :=
  rc40_hallOneSidedA_holds_fin3








theorem rc41_hallBothSided_fails_fin3 :
    rc33_hallBothSided 3 rc32_A3 rc32_B3 = false :=
  rc33_hallBothSided_fin3_refuted



set_option linter.unusedVariables false in
open Classical in






































theorem rc41_reimer_defectcounting :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)},
        (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) →
        Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n))) →
        𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))}
          {K : Finset (Fin n)},
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) →
          (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card)
      ∧ (rc33_HallOneSidedA ↔ rc41_DefectZero)
      ∧ (rc41_DefectZero → rc18_CylBoxReflInter)
      ∧ (rc41_hasCommonCoveringWitness 3 rc40_Aref rc40_Bref {{0}, {1}} = false)
      ∧ (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true)
      ∧ (rc33_hallBothSided 3 rc32_A3 rc32_B3 = false) :=
  ⟨fun n 𝒜 ℬ {𝒯} {K} hKA hKcB hinj =>
      rc41_hall_of_commonWitness_distinctTrace n 𝒜 ℬ hKA hKcB hinj,
    fun n 𝒜 ℬ {𝒯} {K} hKA hKcB => rc41_traceImage_le_biUnion n 𝒜 ℬ hKA hKcB,
    rc41_hallOneSidedA_iff_defectZero,
    rc41_reimer_closes_of_defectZero,
    rc41_commonWitness_collidingTrace_fin3,
    rc41_hallOneSidedA_holds_fin3,
    rc41_hallBothSided_fails_fin3⟩

end StatMech.Walls
