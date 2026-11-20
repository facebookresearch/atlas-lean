/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Code.Walls.rc46butterfly
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









open Classical in





theorem rc47_famCylBox_subset_inter (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ := by
  intro S hS
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  obtain ⟨_, K, L, _, hKA, hLB⟩ := hS
  rw [Finset.mem_inter]
  exact ⟨hKA S rfl, hLB S rfl⟩

open Classical in

theorem rc47_famCylBox_subset_left (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 :=
  (rc47_famCylBox_subset_inter 𝒜 ℬ).trans (Finset.inter_subset_left)

open Classical in

theorem rc47_famCylBox_subset_right (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ ℬ :=
  (rc47_famCylBox_subset_inter 𝒜 ℬ).trans (Finset.inter_subset_right)

open Classical in


theorem rc47_reflInter_subset_left (𝒜 ℬ : Finset (Finset α)) :
    rc10_reflInter 𝒜 ℬ ⊆ 𝒜 := by
  intro R hR
  rw [rc20_mem_reflInter] at hR
  exact hR.1

open Classical in



theorem rc47_reflInter_card_le_right (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) ≤ #ℬ := by
  refine Finset.card_le_card_of_injOn (fun R => Rᶜ) ?_ ?_
  · intro R hR
    rw [Finset.mem_coe, rc20_mem_reflInter] at hR
    exact hR.2
  · intro R _ R' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this

open Classical in



theorem rc47_reflInter_card_le_min (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) ≤ min (#𝒜) (#ℬ) :=
  le_min (Finset.card_le_card (rc47_reflInter_subset_left 𝒜 ℬ))
    (rc47_reflInter_card_le_right 𝒜 ℬ)

open Classical in






theorem rc47_famCylBox_card_le_min (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ min (#𝒜) (#ℬ) :=
  le_min (Finset.card_le_card (rc47_famCylBox_subset_left 𝒜 ℬ))
    (Finset.card_le_card (rc47_famCylBox_subset_right 𝒜 ℬ))











open Classical in



theorem rc47_famCylBox_le_reflInter_of_interCard (𝒜 ℬ : Finset (Finset α))
    (h : #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  (Finset.card_le_card (rc47_famCylBox_subset_inter 𝒜 ℬ)).trans h

open Classical in



theorem rc47_famCylBox_le_reflInter_of_subset (𝒜 ℬ : Finset (Finset α))
    (h : rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  Finset.card_le_card h








def rc47_InterCardDominatesAll : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)

open Classical in




theorem rc47_reimer_closes_of_interCardDominatesAll (h : rc47_InterCardDominatesAll) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc47_famCylBox_le_reflInter_of_interCard 𝒜 ℬ (h n 𝒜 ℬ))


















def rc47_A₁ : Finset (Finset (Fin 3)) := {∅, {0}}


def rc47_B₁ : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {1, 2}}


def rc47_B₂ : Finset (Finset (Fin 3)) := {∅, {1}, {2}, {1, 2}}


def rc47_B₃ : Finset (Finset (Fin 3)) := {∅, {1}, {2}, {1, 2}, {0, 1, 2}}

set_option maxRecDepth 4000 in






theorem rc47_interCard_fires_rc40_fin3 :
    #(rc40_Aref ∩ rc40_Bref) ≤ (rc20_reflInterComp 3 rc40_Aref rc40_Bref).card := by
  rw [rc40_Aref, rc40_Bref]; decide

open Classical in






theorem rc47_wall_rc40_via_interCard :
    #(rc20_famCylBox rc40_Aref rc40_Bref) ≤ #(rc10_reflInter rc40_Aref rc40_Bref) := by
  refine rc47_famCylBox_le_reflInter_of_interCard rc40_Aref rc40_Bref ?_
  have h := rc47_interCard_fires_rc40_fin3
  rwa [rc20_reflInterComp_eq] at h

set_option maxRecDepth 4000 in







theorem rc47_interCard_not_universal_fin3 :
    (rc20_reflInterComp 3 rc47_A₁ rc47_B₁).card < #(rc47_A₁ ∩ rc47_B₁) := by
  rw [rc47_A₁, rc47_B₁]; decide

set_option maxRecDepth 4000 in






theorem rc47_wall_A₁B₁_holds :
    (rc20_famCylBoxComp 3 rc47_A₁ rc47_B₁).card ≤ (rc20_reflInterComp 3 rc47_A₁ rc47_B₁).card := by
  rw [rc47_A₁, rc47_B₁]; decide

set_option maxRecDepth 4000 in





theorem rc47_boxSubReflInter_fires_fin3 :
    rc20_famCylBoxComp 3 rc47_A₁ rc47_B₃ ⊆ rc20_reflInterComp 3 rc47_A₁ rc47_B₃ := by
  rw [rc47_A₁, rc47_B₃]; decide

set_option maxRecDepth 4000 in





theorem rc47_boxSubReflInter_fails_fin3 :
    ¬ (rc20_famCylBoxComp 3 rc47_A₁ rc47_B₂ ⊆ rc20_reflInterComp 3 rc47_A₁ rc47_B₂) := by
  rw [rc47_A₁, rc47_B₂]; decide








open Classical in



theorem rc47_reimer_closes_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue h



open Classical in






























theorem rc47_reimer_sandwich :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc20_famCylBox 𝒜 ℬ) ≤ min (#𝒜) (#ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc10_reflInter 𝒜 ℬ) ≤ min (#𝒜) (#ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc47_InterCardDominatesAll → rc18_CylBoxReflInter)
      ∧ (#(rc20_famCylBox rc40_Aref rc40_Bref) ≤ #(rc10_reflInter rc40_Aref rc40_Bref))
      ∧ ((rc20_reflInterComp 3 rc47_A₁ rc47_B₁).card < #(rc47_A₁ ∩ rc47_B₁))
      ∧ (¬ (rc20_famCylBoxComp 3 rc47_A₁ rc47_B₂ ⊆ rc20_reflInterComp 3 rc47_A₁ rc47_B₂)) :=
  ⟨fun 𝒜 ℬ => rc47_famCylBox_subset_inter 𝒜 ℬ,
    fun 𝒜 ℬ => rc47_famCylBox_card_le_min 𝒜 ℬ,
    fun 𝒜 ℬ => rc47_reflInter_card_le_min 𝒜 ℬ,
    fun 𝒜 ℬ h => rc47_famCylBox_le_reflInter_of_interCard 𝒜 ℬ h,
    rc47_reimer_closes_of_interCardDominatesAll,
    rc47_wall_rc40_via_interCard,
    rc47_interCard_not_universal_fin3,
    rc47_boxSubReflInter_fails_fin3⟩

end StatMech.Walls
