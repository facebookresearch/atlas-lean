/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Code.Walls.rc59doubledcover
import Mathlib.Combinatorics.SetFamily.Compression.Down

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}




theorem rc60_nbhd_eq (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc59_nbhd 𝒜 ℬ S = rc33_admOneSidedA n 𝒜 ℬ S :=
  rc59_nbhd_eq_admOneSidedA 𝒜 ℬ S







open Classical in

theorem rc60_indepHall_empty (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∅ : Finset (Finset (Fin n))).card
      ≤ ((∅ : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  simp

open Classical in





theorem rc60_indepHall_singleton (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ({S} : Finset (Finset (Fin n))).card
      ≤ (({S} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  rw [Finset.card_singleton, Finset.singleton_biUnion, rc59_nbhd_eq_admOneSidedA]
  exact (rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS).card_pos








open Classical in




theorem rc60_self_mem_nbhd_of_reflInter (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc10_reflInter 𝒜 ℬ) : S ∈ rc59_nbhd 𝒜 ℬ S := by
  rw [rc59_nbhd_eq_admOneSidedA, rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  rw [rc20_mem_reflInter] at hS
  refine ⟨Finset.mem_univ _, hS.1, hS.2, univ, Finset.mem_univ _, ?_, rfl⟩
  
  intro T hT
  rw [rc20_traceClass, Finset.mem_filter] at hT
  have : T = S := by
    have h := hT.2
    rwa [Finset.inter_univ, Finset.inter_univ] at h
  rw [this]; exact hS.1















open Classical in



theorem rc60_biUnion_nbhd_subset_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) :
    𝒯.biUnion (rc59_nbhd 𝒜 ℬ) ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [Finset.mem_biUnion] at hR
  obtain ⟨S, _, hRS⟩ := hR
  rw [rc59_nbhd_eq_admOneSidedA] at hRS
  exact rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ S hRS

open Classical in







theorem rc60_wall_of_boxUnionBound (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : #(rc20_famCylBox 𝒜 ℬ)
      ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  h.trans (Finset.card_le_card (rc60_biUnion_nbhd_subset_reflInter 𝒜 ℬ _))

open Classical in


theorem rc60_boxUnionBound_of_indepHall (h : rc59_IndepHall) (m : ℕ)
    (𝒜 ℬ : Finset (Finset (Fin m))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) :=
  h m 𝒜 ℬ (rc20_famCylBox 𝒜 ℬ) (Finset.mem_powerset.mpr (Finset.Subset.refl _))







def rc60_BoxUnionBound : Prop :=
  ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
    #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))

open Classical in


theorem rc60_famCylBoxResidue_of_boxUnionBound (h : rc60_BoxUnionBound) : rc20_FamCylBoxResidue :=
  fun m 𝒜 ℬ => rc60_wall_of_boxUnionBound 𝒜 ℬ (h m 𝒜 ℬ)

open Classical in



theorem rc60_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter
    (rc20_cylBoxReflInter_of_famCylBoxResidue (rc60_famCylBoxResidue_of_boxUnionBound h))

open Classical in



theorem rc60_boxUnionBound_of_indepHall_global (h : rc59_IndepHall) : rc60_BoxUnionBound :=
  fun m 𝒜 ℬ => rc60_boxUnionBound_of_indepHall h m 𝒜 ℬ










open Classical in



theorem rc60_boxUnionBound_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) :=
  rc59_indepHall_fin2 𝒜 ℬ (rc20_famCylBox 𝒜 ℬ)
    (Finset.mem_powerset.mpr (Finset.Subset.refl _))

open Classical in





theorem rc60_boxUnionBound_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3)
      ≤ #((rc20_famCylBox rc32_A3 rc32_B3).biUnion (rc59_nbhd rc32_A3 rc32_B3)) :=
  rc59_indepHall_fin3_refuter (rc20_famCylBox rc32_A3 rc32_B3)
    (Finset.mem_powerset.mpr (Finset.Subset.refl _))

open Classical in

theorem rc60_wall_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) :=
  rc60_wall_of_boxUnionBound rc32_A3 rc32_B3 rc60_boxUnionBound_fin3_refuter

set_option maxRecDepth 4000 in











theorem rc60_reflInter_not_compression_invariant :
    (rc20_reflInterComp 2 (Down.compression 0 ({{0}} : Finset (Finset (Fin 2)))) ({{1}})).card
      ≠ (rc20_reflInterComp 2 ({{0}}) ({{1}})).card := by
  decide










def rc60_A3ex : Finset (Finset (Fin 3)) := {∅, {0}, {2}}


def rc60_B3ex : Finset (Finset (Fin 3)) := {{0}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

set_option maxHeartbeats 4000000 in 
set_option maxRecDepth 10000 in





theorem rc60_hallBothSided_fin3_refuted :
    rc33_hallBothSided 3 rc60_A3ex rc60_B3ex = false := by
  rw [rc60_A3ex, rc60_B3ex]; decide

set_option maxHeartbeats 4000000 in 
set_option maxRecDepth 10000 in





theorem rc60_hallOneSidedA_holds_fin3_contrast :
    rc33_hallOneSidedA 3 rc60_A3ex rc60_B3ex = true := by
  rw [rc60_A3ex, rc60_B3ex]; decide














































open Classical in











theorem rc60_status :
    (rc60_BoxUnionBound → ReimerWprobCore) ∧
    (rc59_IndepHall → rc60_BoxUnionBound) ∧
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) ∧
    (#(rc20_famCylBox rc32_A3 rc32_B3)
        ≤ #((rc20_famCylBox rc32_A3 rc32_B3).biUnion (rc59_nbhd rc32_A3 rc32_B3))) ∧
    (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3)) ∧
    ((rc20_reflInterComp 2 (Down.compression 0 ({{0}} : Finset (Finset (Fin 2)))) ({{1}})).card
        ≠ (rc20_reflInterComp 2 ({{0}}) ({{1}})).card) ∧
    (rc33_hallBothSided 3 rc60_A3ex rc60_B3ex = false) ∧
    (rc33_hallOneSidedA 3 rc60_A3ex rc60_B3ex = true) :=
  ⟨rc60_reimerWprobCore_of_boxUnionBound, rc60_boxUnionBound_of_indepHall_global,
    rc60_boxUnionBound_fin2, rc60_boxUnionBound_fin3_refuter, rc60_wall_fin3_refuter,
    rc60_reflInter_not_compression_invariant, rc60_hallBothSided_fin3_refuted,
    rc60_hallOneSidedA_holds_fin3_contrast⟩

end StatMech.Walls
