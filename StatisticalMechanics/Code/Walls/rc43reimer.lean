/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Code.Walls.rc42multiwitness
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








open Classical in




theorem rc43_famCylBox_symm (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
  ext S
  rw [rc20_famCylBox, rc20_famCylBox, Finset.mem_filter, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨L, K, hKL.symm, hLB, hKA⟩
  · rintro ⟨K, L, hKL, hKB, hLA⟩
    exact ⟨L, K, hKL.symm, hLA, hKB⟩

open Classical in




theorem rc43_reflInter_card_transpose (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
  apply Finset.card_bij (fun S _ => Sᶜ)
  · intro S hS
    rw [rc20_mem_reflInter] at hS
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hS.2, hS.1⟩
  · intro S _ S' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this
  · intro T hT
    rw [rc20_mem_reflInter] at hT
    refine ⟨Tᶜ, ?_, by rw [compl_compl]⟩
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hT.2, hT.1⟩





theorem rc43_cwits_compl (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    (rc42_cwits n 𝒜 ℬ S).image compl = rc42_cwits n ℬ 𝒜 S := by
  ext K
  simp only [Finset.mem_image, rc42_cwits, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨J, ⟨hJA, hJcB⟩, rfl⟩
    exact ⟨hJcB, by rw [compl_compl]; exact hJA⟩
  · rintro ⟨hKB, hKcA⟩
    exact ⟨Kᶜ, ⟨hKcA, by rw [compl_compl]; exact hKB⟩, by rw [compl_compl]⟩



theorem rc43_cwits_card_transpose (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    (rc42_cwits n 𝒜 ℬ S).card = (rc42_cwits n ℬ 𝒜 S).card := by
  rw [← rc43_cwits_compl n 𝒜 ℬ S]
  exact (Finset.card_image_of_injective _ compl_injective).symm










open Classical in











theorem rc43_hall_of_commonCoveringWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  refine Finset.card_le_card_of_injOn (fun S => rc36_R0 S K Kᶜ) ?_ ?_
  · 
    intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨S, hS, ?_⟩
    refine rc42_slice_subset_admCovering n 𝒜 ℬ
      (fun T hT => ⟨(rc20_traceClass_subset_iff n K T 𝒜).mpr (hKA T hT),
        (rc20_traceClass_subset_iff n Kᶜ T ℬ).mpr (hKcB T hT)⟩) hS ?_
    exact rc36_R0_mem_traceSlice 𝒜 ℬ disjoint_compl_right (hKA S hS) (hKcB S hS)
  · 
    intro S _ S' _ h
    exact rc40_R0_injOn_of_cover K Kᶜ disjoint_compl_right (by simp) h

open Classical in





theorem rc43_commonCoveringWitness_generalises_rc41 (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card :=
  rc43_hall_of_commonCoveringWitness n 𝒜 ℬ hKA hKcB











def rc43_GlobalCommonWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Prop :=
  ∃ K : Finset (Fin n),
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ)

open Classical in




theorem rc43_hallCovering_of_globalCommonWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc43_GlobalCommonWitness n 𝒜 ℬ) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  obtain ⟨K, hKA, hKcB⟩ := h
  intro 𝒯 h𝒯
  rw [Finset.mem_powerset] at h𝒯
  exact rc43_hall_of_commonCoveringWitness n 𝒜 ℬ
    (fun S hS => hKA S (h𝒯 hS)) (fun S hS => hKcB S (h𝒯 hS))

open Classical in






theorem rc43_famCylBox_le_reflInter_of_globalCommonWitness (n : ℕ)
    (𝒜 ℬ : Finset (Finset (Fin n))) (h : rc43_GlobalCommonWitness n 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  have hHall := rc43_hallCovering_of_globalCommonWitness n 𝒜 ℬ h
    (rc20_famCylBox 𝒜 ℬ) (Finset.mem_powerset.mpr (Finset.Subset.refl _))
  refine hHall.trans (Finset.card_le_card ?_)
  intro R hR
  rw [Finset.mem_biUnion] at hR
  obtain ⟨S, _, hRS⟩ := hR
  exact rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ S
    (rc42_admCovering_subset_admOneSidedA n 𝒜 ℬ S hRS)



def rc43_GlobalCommonWitnessAll : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), rc43_GlobalCommonWitness n 𝒜 ℬ

open Classical in






theorem rc43_reimer_closes_of_globalCommonWitnessAll (h : rc43_GlobalCommonWitnessAll) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc43_famCylBox_le_reflInter_of_globalCommonWitness n 𝒜 ℬ (h n 𝒜 ℬ))












def rc43_globalCommonWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∃ K : Finset (Fin n),
    (∀ S ∈ rc21_boxComp n 𝒜 ℬ, rc20_traceClass n K S ⊆ 𝒜) ∧
    (∀ S ∈ rc21_boxComp n 𝒜 ℬ, rc20_traceClass n Kᶜ S ⊆ ℬ))

open Classical in



theorem rc43_globalCommonWitness_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc43_globalCommonWitness n 𝒜 ℬ = true) :
    rc43_GlobalCommonWitness n 𝒜 ℬ := by
  rw [rc43_globalCommonWitness, decide_eq_true_eq, rc21_boxComp_eq] at h
  obtain ⟨K, hKA, hKcB⟩ := h
  refine ⟨K, ?_, ?_⟩
  · intro S hS T hT
    exact (rc20_traceClass_subset_iff n K S 𝒜).mp (hKA S hS) T hT
  · intro S hS T hT
    exact (rc20_traceClass_subset_iff n Kᶜ S ℬ).mp (hKcB S hS) T hT

set_option maxRecDepth 4000 in








theorem rc43_globalCommonWitness_refuter_false :
    rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false := by
  rw [rc40_Aref, rc40_Bref, rc43_globalCommonWitness]; decide






theorem rc43_globalCommonWitness_univ_fin2 :
    rc43_globalCommonWitness 2 Finset.univ Finset.univ = true := by
  decide

open Classical in






theorem rc43_residue_named :
    (rc43_GlobalCommonWitnessAll → rc18_CylBoxReflInter)
      ∧ (rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false)
      ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true) :=
  ⟨rc43_reimer_closes_of_globalCommonWitnessAll,
    rc43_globalCommonWitness_refuter_false,
    rc42_hallCovering_holds_fin3⟩



set_option linter.unusedVariables false in
open Classical in






































theorem rc43_reimer_symmetry_and_globalwitness :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))}
            {K : Finset (Fin n)},
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
          (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) →
          𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
          rc43_GlobalCommonWitness n 𝒜 ℬ →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc43_GlobalCommonWitnessAll → rc18_CylBoxReflInter)
      ∧ (rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false)
      ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true)
      ∧ (rc43_globalCommonWitness 2 Finset.univ Finset.univ = true) :=
  ⟨fun 𝒜 ℬ => rc43_famCylBox_symm 𝒜 ℬ,
    fun 𝒜 ℬ => rc43_reflInter_card_transpose 𝒜 ℬ,
    fun n 𝒜 ℬ {𝒯} {K} hKA hKcB => rc43_hall_of_commonCoveringWitness n 𝒜 ℬ hKA hKcB,
    fun n 𝒜 ℬ h => rc43_famCylBox_le_reflInter_of_globalCommonWitness n 𝒜 ℬ h,
    rc43_reimer_closes_of_globalCommonWitnessAll,
    rc43_globalCommonWitness_refuter_false,
    rc42_hallCovering_holds_fin3,
    rc43_globalCommonWitness_univ_fin2⟩

end StatMech.Walls
