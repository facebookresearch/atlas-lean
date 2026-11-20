/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Code.Walls.rc33nonlocal
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]















theorem rc34_reflInter_symmDiff_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K L : Finset (Fin n)} (hKL : Disjoint K L)
    (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
    symmDiff S L ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
  have hmem := rc21_symmDiff_mem_reflInter hKL hKA hLB
  rw [rc20_mem_reflInter] at hmem
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  refine ⟨Finset.mem_univ _, hmem.1, hmem.2, K, Finset.mem_univ _, ?_, ?_⟩
  · exact (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA
  · exact rc21_symmDiff_inter_left S K L hKL

open Classical in




theorem rc34_self_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K : Finset (Fin n)} (hSRI : S ∈ rc10_reflInter 𝒜 ℬ)
    (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) :
    S ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
  rw [rc20_mem_reflInter] at hSRI
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨Finset.mem_univ _, hSRI.1, hSRI.2, K, Finset.mem_univ _,
    (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, rfl⟩









open Classical in









theorem rc34_admComp_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) :
    rc21_admComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc21_admComp, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, K, _, L, _, _, hKA, hLB, hRK, hRL⟩ := hR
  have hKA' : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜 :=
    (rc20_traceClass_subset_iff n K S 𝒜).mp hKA
  have hLB' : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ :=
    (rc20_traceClass_subset_iff n L S ℬ).mp hLB
  have hmem := rc21_localRefl_mem_reflInter hKA' hLB' hRK hRL
  rw [rc20_mem_reflInter] at hmem
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨Finset.mem_univ _, hmem.1, hmem.2, K, Finset.mem_univ _, hKA, hRK⟩











theorem rc34_hall_of_subgraph {β : Type*} [DecidableEq β] (𝒢 : Finset (Finset β))
    (t t' : Finset β → Finset (Finset β)) (hsub : ∀ S ∈ 𝒢, t S ⊆ t' S)
    (hHall : ∀ 𝒯 ∈ 𝒢.powerset, 𝒯.card ≤ (𝒯.biUnion t).card) :
    ∀ 𝒯 ∈ 𝒢.powerset, 𝒯.card ≤ (𝒯.biUnion t').card := by
  intro 𝒯 h𝒯
  rw [Finset.mem_powerset] at h𝒯
  refine le_trans (hHall 𝒯 (Finset.mem_powerset.mpr h𝒯)) ?_
  exact Finset.card_le_card (Finset.biUnion_mono (fun S hS => hsub S (h𝒯 hS)))

open Classical in







theorem rc34_hallOneSidedA_of_localReflHall (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card :=
  rc34_hall_of_subgraph (rc20_famCylBox 𝒜 ℬ) (rc21_admComp n 𝒜 ℬ) (rc33_admOneSidedA n 𝒜 ℬ)
    (fun S _ => rc34_admComp_subset_admOneSidedA n 𝒜 ℬ S) hHall





















def rc34_A3 : Finset (Finset (Fin 3)) := {{0}, {0, 1, 2}}


def rc34_B3 : Finset (Finset (Fin 3)) := {{0, 1}, {0, 2}, {1}, {2}}

set_option maxHeartbeats 1000000 in



theorem rc34_card_boxDoubled_A3B3 :
    (boxDoubled rc34_A3 rc34_B3).card = 2 := by
  rw [card_boxDoubled, rc34_A3, rc34_B3]; decide

set_option maxHeartbeats 1000000 in




theorem rc34_card_boxDoubled_compressed :
    (boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3)).card = 4 := by
  rw [card_boxDoubled, rc34_A3, rc34_B3]; decide








theorem rc34_doubleCompress_ne_componentBox :
    doubleCompress 0 (boxDoubled rc34_A3 rc34_B3)
      ≠ boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3) := by
  intro h
  have hL : (doubleCompress 0 (boxDoubled rc34_A3 rc34_B3)).card = 2 := by
    rw [doubleCompress_card, rc34_card_boxDoubled_A3B3]
  have hR := rc34_card_boxDoubled_compressed
  rw [h] at hL
  rw [hL] at hR
  exact absurd hR (by norm_num)













theorem rc34_localReflHall_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc21_localReflSearch n 𝒜 ℬ = true) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card := by
  rw [rc21_localReflSearch, decide_eq_true_eq, rc21_boxComp_eq] at h
  exact h





theorem rc34_localReflSearch_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    rc21_localReflSearch 1 𝒜 ℬ = true := by revert 𝒜 ℬ; decide

open Classical in






theorem rc34_wall_fin1_via_subgraph (𝒜 ℬ : Finset (Finset (Fin 1))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc33_wall_of_hallOneSidedA 1 𝒜 ℬ
    (rc34_hallOneSidedA_of_localReflHall 1 𝒜 ℬ
      (rc34_localReflHall_prop_of_bool 1 𝒜 ℬ (rc34_localReflSearch_fin1 𝒜 ℬ)))



set_option linter.unusedVariables false in
open Classical in



























theorem rc34_reimer_butterfly :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
        rc21_admComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
          (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
            𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card) →
          (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
            𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 1))),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (doubleCompress 0 (boxDoubled rc34_A3 rc34_B3)
          ≠ boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3)) :=
  ⟨rc34_admComp_subset_admOneSidedA,
    rc34_hallOneSidedA_of_localReflHall,
    rc34_wall_fin1_via_subgraph,
    rc34_doubleCompress_ne_componentBox⟩

end StatMech.Walls
