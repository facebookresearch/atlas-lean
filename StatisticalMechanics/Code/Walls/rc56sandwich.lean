/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Code.Walls.rc55nonproduct
import Code.Walls.rc47reimer

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










def rc56_hasWitness (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Prop :=
  ∃ K L : Finset α, Disjoint K L ∧
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ)

open Classical in
noncomputable instance rc56_hasWitness_decidablePred (𝒜 ℬ : Finset (Finset α)) :
    DecidablePred (rc56_hasWitness 𝒜 ℬ) :=
  fun _ => Classical.propDecidable _

open Classical in


theorem rc56_mem_famCylBox_iff_witness (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc20_famCylBox 𝒜 ℬ ↔ rc56_hasWitness 𝒜 ℬ S :=
  rc21_mem_famCylBox 𝒜 ℬ S

omit [Fintype α] in



theorem rc56_mem_inter_of_hasWitness (𝒜 ℬ : Finset (Finset α)) {S : Finset α}
    (h : rc56_hasWitness 𝒜 ℬ S) : S ∈ 𝒜 ∩ ℬ := by
  obtain ⟨K, L, _, hKA, hLB⟩ := h
  rw [Finset.mem_inter]
  exact ⟨hKA S rfl, hLB S rfl⟩

open Classical in






theorem rc56_famCylBox_eq_inter_filter (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = (𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) := by
  ext S
  rw [Finset.mem_filter, rc56_mem_famCylBox_iff_witness]
  constructor
  · intro h
    exact ⟨rc56_mem_inter_of_hasWitness 𝒜 ℬ h, h⟩
  · intro h
    exact h.2

open Classical in



theorem rc56_famCylBox_card_eq_witnessCount (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) = #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) := by
  rw [rc56_famCylBox_eq_inter_filter]












open Classical in




theorem rc56_famCylBox_symm (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
  ext S
  rw [rc56_mem_famCylBox_iff_witness, rc56_mem_famCylBox_iff_witness]
  constructor
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨L, K, hKL.symm, hLB, hKA⟩
  · rintro ⟨K, L, hKL, hKB, hLA⟩
    exact ⟨L, K, hKL.symm, hLA, hKB⟩

open Classical in


theorem rc56_famCylBox_card_symm (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) = #(rc20_famCylBox ℬ 𝒜) := by
  rw [rc56_famCylBox_symm]

open Classical in




theorem rc56_reflInter_card_symm (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
  refine Finset.card_bij (fun S _ => Sᶜ) ?_ ?_ ?_
  · intro S hS
    rw [rc20_mem_reflInter] at hS
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hS.2, hS.1⟩
  · intro S _ S' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this
  · intro R hR
    rw [rc20_mem_reflInter] at hR
    refine ⟨Rᶜ, ?_, compl_compl R⟩
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hR.2, hR.1⟩








open Classical in



theorem rc56_reflInter_card_eq_interComplFam (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(𝒜 ∩ rc22_complFam ℬ) := by
  rw [rc22_reflInter_eq_inter_complFam]

open Classical in






theorem rc56_wall_iff_witnessedInter (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
      #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) := by
  rw [rc56_famCylBox_card_eq_witnessCount, rc56_reflInter_card_eq_interComplFam]



def rc56_WitnessedInterResidue : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ)

open Classical in




theorem rc56_witnessedInterResidue_iff_famCylBoxResidue :
    rc56_WitnessedInterResidue ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    rw [rc56_wall_iff_witnessedInter]; exact h n 𝒜 ℬ
  · intro h n 𝒜 ℬ
    rw [← rc56_wall_iff_witnessedInter]; exact h n 𝒜 ℬ

open Classical in


theorem rc56_reimer_closes_of_witnessedInterResidue (h : rc56_WitnessedInterResidue) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (rc56_witnessedInterResidue_iff_famCylBoxResidue.mp h)






















def rc56_reflImageSet (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (∃ S ∈ rc20_famCylBoxComp n 𝒜 ℬ,
    ∃ K ∈ (univ : Finset (Finset (Fin n))), ∃ L ∈ (univ : Finset (Finset (Fin n))),
      Disjoint K L ∧ rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ ∧
        R = symmDiff S L) = true)


def rc56_Ares : Finset (Finset (Fin 3)) := {∅, {0}, {1}}



def rc56_Bres : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

set_option maxRecDepth 4000 in

theorem rc56_box_res_card :
    (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card = 2 := by
  rw [rc56_Ares, rc56_Bres]; decide

set_option maxRecDepth 4000 in

theorem rc56_reflInter_res_card :
    (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card = 3 := by
  rw [rc56_Ares, rc56_Bres]; decide

set_option maxRecDepth 4000 in



theorem rc56_reflImageSet_res_card :
    (rc56_reflImageSet 3 rc56_Ares rc56_Bres).card = 1 := by
  rw [rc56_Ares, rc56_Bres]; decide

set_option maxRecDepth 4000 in







theorem rc56_symmDiff_collides_fin3 :
    (rc56_reflImageSet 3 rc56_Ares rc56_Bres).card
      < (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card := by
  rw [rc56_reflImageSet_res_card, rc56_box_res_card]; norm_num

set_option maxRecDepth 4000 in




theorem rc56_wall_holds_on_res :
    (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card
      ≤ (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card := by
  rw [rc56_box_res_card, rc56_reflInter_res_card]; norm_num



open Classical in


theorem rc56_reimer_closes_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue h

open Classical in

theorem rc56_reimerWprobCore_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) : ReimerWprobCore :=
  rc55_reimerWprobCore_of_famCylBoxResidue h



open Classical in































theorem rc56_reimer_sandwich :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        rc20_famCylBox 𝒜 ℬ = (𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
            #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ))
      ∧ (rc56_WitnessedInterResidue ↔ rc20_FamCylBoxResidue)
      ∧ (rc56_WitnessedInterResidue → rc18_CylBoxReflInter)
      ∧ ((rc56_reflImageSet 3 rc56_Ares rc56_Bres).card
          < (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card)
      ∧ ((rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card
          ≤ (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card) :=
  ⟨fun 𝒜 ℬ => rc56_famCylBox_eq_inter_filter 𝒜 ℬ,
    fun 𝒜 ℬ => rc56_famCylBox_symm 𝒜 ℬ,
    fun 𝒜 ℬ => rc56_reflInter_card_symm 𝒜 ℬ,
    fun 𝒜 ℬ => rc56_wall_iff_witnessedInter 𝒜 ℬ,
    rc56_witnessedInterResidue_iff_famCylBoxResidue,
    rc56_reimer_closes_of_witnessedInterResidue,
    rc56_symmDiff_collides_fin3,
    rc56_wall_holds_on_res⟩

end StatMech.Walls
