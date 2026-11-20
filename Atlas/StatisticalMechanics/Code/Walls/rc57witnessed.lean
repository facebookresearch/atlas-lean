/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Code.Walls.rc56sandwich
import Code.Walls.rc21persupport
import Mathlib.Combinatorics.Hall.Basic

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










open Classical in






theorem rc57_witnessedInter_iff_injection (𝒜 ℬ : Finset (Finset α)) :
    #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) ↔
      Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset α))
        ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset α))) := by
  rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_coe, Fintype.card_coe]
















def rc57_NaturalSDR : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∃ f : Finset (Fin n) → Finset (Fin n),
      Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧
      ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc21_admComp n 𝒜 ℬ S

open Classical in





theorem rc57_naturalSDR_closes_residue (h : rc57_NaturalSDR) : rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  obtain ⟨f, hinj, hmem⟩ := h n 𝒜 ℬ
  refine Finset.card_le_card_of_injOn f (fun S hS => ?_) hinj
  exact rc21_admComp_subset_reflInter n 𝒜 ℬ S (hmem S hS)

open Classical in


theorem rc57_reimer_closes_of_naturalSDR (h : rc57_NaturalSDR) : rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue (rc57_naturalSDR_closes_residue h)

open Classical in






theorem rc57_hall_iff_sdr (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒮 : Finset (rc20_famCylBox 𝒜 ℬ),
        #𝒮 ≤ #(𝒮.biUnion (fun S => rc21_admComp n 𝒜 ℬ (S : Finset (Fin n))))) ↔
      ∃ f : (rc20_famCylBox 𝒜 ℬ) → Finset (Fin n),
        Function.Injective f ∧
          ∀ S : (rc20_famCylBox 𝒜 ℬ), f S ∈ rc21_admComp n 𝒜 ℬ (S : Finset (Fin n)) :=
  Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun S : (rc20_famCylBox 𝒜 ℬ) =>
      rc21_admComp n 𝒜 ℬ (S : Finset (Fin n)))










def rc57_Anat : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {0, 1}, {2}, {0, 2}}


def rc57_Bnat : Finset (Finset (Fin 3)) := {{1}, {2}, {1, 2}}





noncomputable def rc57_natNbhd (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  ((rc20_famCylBoxComp n 𝒜 ℬ).biUnion (fun S => rc21_admComp n 𝒜 ℬ S))
    ∪ (rc20_famCylBoxComp n 𝒜 ℬ ∩ rc20_reflInterComp n 𝒜 ℬ)

set_option maxRecDepth 4000 in

theorem rc57_box_natRes_card :
    (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card = 2 := by
  rw [rc57_Anat, rc57_Bnat]; decide

set_option maxRecDepth 4000 in


theorem rc57_reflInter_natRes_card :
    (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card = 3 := by
  rw [rc57_Anat, rc57_Bnat]; decide

set_option maxRecDepth 4000 in




theorem rc57_natNbhd_natRes_card :
    (rc57_natNbhd 3 rc57_Anat rc57_Bnat).card = 1 := by
  rw [rc57_natNbhd, rc57_Anat, rc57_Bnat]; decide

set_option maxRecDepth 4000 in








theorem rc57_naturalHall_fails_fin3 :
    (rc57_natNbhd 3 rc57_Anat rc57_Bnat).card
      < (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card := by
  rw [rc57_natNbhd_natRes_card, rc57_box_natRes_card]; norm_num

set_option maxRecDepth 4000 in






theorem rc57_wall_holds_on_natRes :
    (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card
      ≤ (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card := by
  rw [rc57_box_natRes_card, rc57_reflInter_natRes_card]; norm_num








open Classical in


def rc57_ReflMatching : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset (Fin n)))
      ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset (Fin n))))

open Classical in


theorem rc57_reflMatching_iff_witnessedInterResidue :
    rc57_ReflMatching ↔ rc56_WitnessedInterResidue := by
  constructor
  · intro h n 𝒜 ℬ
    exact (rc57_witnessedInter_iff_injection 𝒜 ℬ).mpr (h n 𝒜 ℬ)
  · intro h n 𝒜 ℬ
    exact (rc57_witnessedInter_iff_injection 𝒜 ℬ).mp (h n 𝒜 ℬ)

open Classical in


theorem rc57_reimer_closes_of_reflMatching (h : rc57_ReflMatching) : rc18_CylBoxReflInter :=
  rc56_reimer_closes_of_witnessedInterResidue
    (rc57_reflMatching_iff_witnessedInterResidue.mp h)



open Classical in





























theorem rc57_reimer_matching :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) ↔
          Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset (Fin 3)))
            ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset (Fin 3)))))
      ∧ (rc57_ReflMatching ↔ rc56_WitnessedInterResidue)
      ∧ (rc57_ReflMatching → rc18_CylBoxReflInter)
      ∧ (rc57_NaturalSDR → rc18_CylBoxReflInter)
      ∧ ((rc57_natNbhd 3 rc57_Anat rc57_Bnat).card
          < (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card)
      ∧ ((rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card
          ≤ (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card) :=
  ⟨fun 𝒜 ℬ => rc57_witnessedInter_iff_injection 𝒜 ℬ,
    rc57_reflMatching_iff_witnessedInterResidue,
    rc57_reimer_closes_of_reflMatching,
    rc57_reimer_closes_of_naturalSDR,
    rc57_naturalHall_fails_fin3,
    rc57_wall_holds_on_natRes⟩

end StatMech.Walls
