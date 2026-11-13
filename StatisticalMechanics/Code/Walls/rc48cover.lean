/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Code.Walls.rc47reimer

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]











open Classical in




theorem rc48_compl_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) (hSc : Sᶜ ∈ 𝒜) :
    Sᶜ ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter, compl_compl]
  exact ⟨hSc, rc47_famCylBox_subset_right 𝒜 ℬ hS⟩

open Classical in






theorem rc48_famCylBox_le_reflInter_of_complSubset (𝒜 ℬ : Finset (Finset α))
    (h : ∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  refine Finset.card_le_card_of_injOn (fun S => Sᶜ) ?_ ?_
  · intro S hS
    rw [Finset.mem_coe] at hS
    exact rc48_compl_mem_reflInter hS (h S hS)
  · intro S _ S' _ hSS'
    have := congrArg (compl : Finset α → Finset α) hSS'
    rwa [compl_compl, compl_compl] at this









open Classical in


theorem rc48_reflInter_mono_left {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    rc10_reflInter 𝒜 ℬ ⊆ rc10_reflInter 𝒜' ℬ := by
  intro S hS
  rw [rc20_mem_reflInter] at hS ⊢
  exact ⟨h hS.1, hS.2⟩

open Classical in


theorem rc48_reflInter_mono_right {𝒜 ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    rc10_reflInter 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ' := by
  intro S hS
  rw [rc20_mem_reflInter] at hS ⊢
  exact ⟨hS.1, h hS.2⟩







open Classical in





def rc48_CoverAll : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨
    rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜)

open Classical in




theorem rc48_wall_of_cover (𝒜 ℬ : Finset (Finset α))
    (h : #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨
      rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨
      (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rcases h with h | h | h
  · exact rc47_famCylBox_le_reflInter_of_interCard 𝒜 ℬ h
  · exact rc47_famCylBox_le_reflInter_of_subset 𝒜 ℬ h
  · exact rc48_famCylBox_le_reflInter_of_complSubset 𝒜 ℬ h

open Classical in




theorem rc48_reimer_closes_of_coverAll (h : rc48_CoverAll) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc48_wall_of_cover 𝒜 ℬ (h n 𝒜 ℬ))




















def rc48_C₁ : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {2}}


def rc48_D₁ : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {0, 1, 2}}


def rc48_A₂ : Finset (Finset (Fin 3)) := {∅, {0}}


def rc48_B₂ : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {1, 2}}


def rc48_E₂ : Finset (Finset (Fin 3)) := {{0}, {1}, {2}, {1, 2}}

set_option maxRecDepth 4000 in






theorem rc48_complSubset_fires_fin3 :
    ∀ S ∈ rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁, Sᶜ ∈ rc48_C₁ := by
  rw [rc48_C₁, rc48_D₁]; decide

set_option maxRecDepth 4000 in




theorem rc48_boxSubReflInter_fails_C₁D₁_fin3 :
    ¬ (rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁ ⊆ rc20_reflInterComp 3 rc48_C₁ rc48_D₁) := by
  rw [rc48_C₁, rc48_D₁]; decide

set_option maxRecDepth 4000 in





theorem rc48_interCard_fails_C₁D₁_fin3 :
    (rc20_reflInterComp 3 rc48_C₁ rc48_D₁).card < #(rc48_C₁ ∩ rc48_D₁) := by
  rw [rc48_C₁, rc48_D₁]; decide

open Classical in





theorem rc48_wall_C₁D₁_via_complSubset :
    #(rc20_famCylBox rc48_C₁ rc48_D₁) ≤ #(rc10_reflInter rc48_C₁ rc48_D₁) := by
  refine rc48_famCylBox_le_reflInter_of_complSubset rc48_C₁ rc48_D₁ ?_
  intro S hS
  have h := rc48_complSubset_fires_fin3 S
  rw [rc20_famCylBoxComp_eq] at h
  exact h hS

set_option maxRecDepth 4000 in













theorem rc48_residual_c1_fails_fin3 :
    (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card < #(rc48_A₂ ∩ rc48_B₂) := by
  rw [rc48_A₂, rc48_B₂]; decide

set_option maxRecDepth 4000 in

theorem rc48_residual_c2_fails_fin3 :
    ¬ (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂ ⊆ rc20_reflInterComp 3 rc48_A₂ rc48_B₂) := by
  rw [rc48_A₂, rc48_B₂]; decide

set_option maxRecDepth 4000 in

theorem rc48_residual_c3_fails_fin3 :
    ¬ (∀ S ∈ rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂, Sᶜ ∈ rc48_A₂) := by
  rw [rc48_A₂, rc48_B₂]; decide

set_option maxRecDepth 4000 in





theorem rc48_wall_A₂B₂_holds :
    (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card := by
  rw [rc48_A₂, rc48_B₂]; decide









def rc48_downCompress (n : ℕ) (i : Fin n) (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  𝒜.image (fun S => if i ∈ S ∧ S.erase i ∉ 𝒜 then S.erase i else S)

set_option maxRecDepth 4000 in







theorem rc48_famCylBox_not_compressionInvariant :
    (rc20_famCylBoxComp 3 (rc48_downCompress 3 0 rc48_A₂)
        (rc48_downCompress 3 0 rc48_E₂)).card
      ≠ (rc20_famCylBoxComp 3 rc48_A₂ rc48_E₂).card := by
  rw [rc48_A₂, rc48_E₂, rc48_downCompress, rc48_downCompress]; decide



open Classical in







































theorem rc48_reimer_threeway_cover :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) →
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨
            rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨
            (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc48_CoverAll → rc18_CylBoxReflInter)
      ∧ (#(rc20_famCylBox rc48_C₁ rc48_D₁) ≤ #(rc10_reflInter rc48_C₁ rc48_D₁))
      ∧ (¬ (rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁ ⊆ rc20_reflInterComp 3 rc48_C₁ rc48_D₁))
      ∧ ((rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card < #(rc48_A₂ ∩ rc48_B₂))
      ∧ ((rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card)
      ∧ ((rc20_famCylBoxComp 3 (rc48_downCompress 3 0 rc48_A₂)
            (rc48_downCompress 3 0 rc48_E₂)).card
          ≠ (rc20_famCylBoxComp 3 rc48_A₂ rc48_E₂).card) :=
  ⟨fun 𝒜 ℬ h => rc48_famCylBox_le_reflInter_of_complSubset 𝒜 ℬ h,
    fun 𝒜 ℬ h => rc48_wall_of_cover 𝒜 ℬ h,
    rc48_reimer_closes_of_coverAll,
    rc48_wall_C₁D₁_via_complSubset,
    rc48_boxSubReflInter_fails_C₁D₁_fin3,
    rc48_residual_c1_fails_fin3,
    rc48_wall_A₂B₂_holds,
    rc48_famCylBox_not_compressionInvariant⟩

end StatMech.Walls
