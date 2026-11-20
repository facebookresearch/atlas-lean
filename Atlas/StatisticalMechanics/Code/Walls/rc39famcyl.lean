/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Code.Walls.rc38butterflymono
import Code.Walls.rc22doublecover
import Code.Walls.rc23boxmono

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







open Classical in


theorem rc39_reflInter_right_univ (𝒜 : Finset (Finset α)) :
    rc10_reflInter 𝒜 univ = 𝒜 := by
  ext S; rw [rc20_mem_reflInter]; simp [Finset.mem_univ]

open Classical in



theorem rc39_famCylBox_right_univ_subset (𝒜 : Finset (Finset α)) :
    rc20_famCylBox 𝒜 univ ⊆ 𝒜 := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, _, hKA, _⟩ := hS
  exact hKA S rfl

open Classical in



theorem rc39_famCylBox_le_reflInter_right_univ (𝒜 : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ) := by
  rw [rc39_reflInter_right_univ]
  exact Finset.card_le_card (rc39_famCylBox_right_univ_subset 𝒜)

open Classical in



theorem rc39_famCylBox_left_univ_subset (ℬ : Finset (Finset α)) :
    rc20_famCylBox univ ℬ ⊆ ℬ := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, _, _, hLB⟩ := hS
  exact hLB S rfl

open Classical in



theorem rc39_card_reflInter_left_univ (ℬ : Finset (Finset α)) :
    #(rc10_reflInter univ ℬ) = #ℬ := by
  rw [rc22_reflInter_eq_inter_complFam, Finset.univ_inter, rc22_card_complFam]

open Classical in



theorem rc39_famCylBox_le_reflInter_left_univ (ℬ : Finset (Finset α)) :
    #(rc20_famCylBox univ ℬ) ≤ #(rc10_reflInter univ ℬ) := by
  rw [rc39_card_reflInter_left_univ]
  exact Finset.card_le_card (rc39_famCylBox_left_univ_subset ℬ)








open Classical in




theorem rc39_famCylBox_le_reflInter_of_monotone {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h : (IsUpperSet (𝒜 : Set (Finset (Fin n))) ∧ IsUpperSet (ℬ : Set (Finset (Fin n))))
        ∨ (IsLowerSet (𝒜 : Set (Finset (Fin n))) ∧ IsLowerSet (ℬ : Set (Finset (Fin n))))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rcases h with ⟨h𝒜, hℬ⟩ | ⟨h𝒜, hℬ⟩
  · exact rc22_famCylBox_le_reflInter_of_upperSet h𝒜 hℬ
  · exact rc23_boxDownsetBase_proof h𝒜 hℬ















def dc39_A : Finset (Finset (Fin 3)) := {{2}, {1, 2}, {0, 1, 2}}

def dc39_B : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

def dc39_C : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

def dc39_D : Finset (Finset (Fin 3)) := {∅, {1}, {0, 1}}

def dc39_E : Finset (Finset (Fin 3)) := {{0, 1}}

def dc39_F : Finset (Finset (Fin 3)) := {{0, 2}}












theorem rc39_deficit_downDown_strictIncrease :
    (#(rc10_reflInter dc39_A dc39_B) - #(rc20_famCylBox dc39_A dc39_B))
      < (#(rc10_reflInter (Down.compression 0 dc39_A) (Down.compression 0 dc39_B))
          - #(rc20_famCylBox (Down.compression 0 dc39_A) (Down.compression 0 dc39_B))) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq, ← rc20_famCylBoxComp_eq,
    ← rc20_reflInterComp_eq]
  decide






theorem rc39_deficitMono_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
        (#(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
          - #(rc20_famCylBox (Down.compression i 𝒜) (Down.compression i ℬ)))
        ≤ (#(rc10_reflInter 𝒜 ℬ) - #(rc20_famCylBox 𝒜 ℬ))) := by
  intro h
  have := h 3 dc39_A dc39_B 0
  exact absurd this (not_le.mpr rc39_deficit_downDown_strictIncrease)










theorem rc39_famCylBox_oneSide_strictDecrease :
    #(rc20_famCylBox (Down.compression 0 dc39_C) dc39_D)
      < #(rc20_famCylBox dc39_C dc39_D) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  decide





theorem rc39_boxOneSideMono_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) ℬ)) := by
  intro h
  have := h 3 dc39_C dc39_D 0
  exact absurd this (not_le.mpr rc39_famCylBox_oneSide_strictDecrease)











theorem rc39_reflInter_oneSide_strictIncrease :
    #(rc10_reflInter dc39_E dc39_F)
      < #(rc10_reflInter (Down.compression 0 dc39_E) dc39_F) := by
  rw [← rc20_reflInterComp_eq, ← rc20_reflInterComp_eq]
  decide






theorem rc39_reflInter_oneSide_antitone_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
        #(rc10_reflInter (Down.compression i 𝒜) ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
  intro h
  have := h 3 dc39_E dc39_F 0
  exact absurd this (not_le.mpr rc39_reflInter_oneSide_strictIncrease)










theorem rc39_wall_holds_deficitWitness :
    #(rc20_famCylBox dc39_A dc39_B) ≤ #(rc10_reflInter dc39_A dc39_B) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]; decide



theorem rc39_wall_holds_boxOneSideWitness :
    #(rc20_famCylBox dc39_C dc39_D) ≤ #(rc10_reflInter dc39_C dc39_D) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]; decide



theorem rc39_wall_holds_reflOneSideWitness :
    #(rc20_famCylBox dc39_E dc39_F) ≤ #(rc10_reflInter dc39_E dc39_F) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]; decide



set_option linter.unusedVariables false in
open Classical in












































theorem rc39_reimer_famcyl :
    (∀ (𝒜 : Finset (Finset α)), #(rc20_famCylBox 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ))
      ∧ (∀ (ℬ : Finset (Finset α)), #(rc20_famCylBox univ ℬ) ≤ #(rc10_reflInter univ ℬ))
      ∧ (∀ {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))},
          (IsUpperSet (𝒜 : Set (Finset (Fin n))) ∧ IsUpperSet (ℬ : Set (Finset (Fin n))))
            ∨ (IsLowerSet (𝒜 : Set (Finset (Fin n))) ∧ IsLowerSet (ℬ : Set (Finset (Fin n)))) →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
          (#(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
            - #(rc20_famCylBox (Down.compression i 𝒜) (Down.compression i ℬ)))
          ≤ (#(rc10_reflInter 𝒜 ℬ) - #(rc20_famCylBox 𝒜 ℬ))))
      ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) ℬ)))
      ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
          #(rc10_reflInter (Down.compression i 𝒜) ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))) :=
  ⟨rc39_famCylBox_le_reflInter_right_univ,
    rc39_famCylBox_le_reflInter_left_univ,
    fun {_ _ _} h => rc39_famCylBox_le_reflInter_of_monotone h,
    rc39_deficitMono_false,
    rc39_boxOneSideMono_false,
    rc39_reflInter_oneSide_antitone_false⟩

end StatMech.Walls
