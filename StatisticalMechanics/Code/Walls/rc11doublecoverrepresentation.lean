/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Code.Walls.rc10core
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







omit [Fintype α] in


theorem rc11_card_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card :=
  card_boxDoubled 𝒜 ℬ







open Classical in


theorem rc11_isUpperSet_boxSupp (𝒜 ℬ : Finset (Finset α)) :
    IsUpperSet ((rc10_boxSupp 𝒜 ℬ) : Set (Finset α)) := by
  intro S T hST hS
  simp only [Finset.mem_coe, rc10_boxSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  obtain ⟨K, L, hKL, hKS, hLS, hK, hL⟩ := hS
  exact ⟨K, L, hKL, hKS.trans hST, hLS.trans hST, hK, hL⟩







open Classical in









theorem rc11_boxSupp_iff_doubled (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc10_boxSupp 𝒜 ℬ ↔
      ∃ U ∈ boxDoubled 𝒜 ℬ, ∃ K L : Finset α, U = dbl K L ∧ K ∪ L ⊆ S := by
  rw [rc10_boxSupp, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨K, L, hKL, hKS, hLS, hK𝒜, hLℬ⟩
    refine ⟨dbl K L, ?_, K, L, rfl, ?_⟩
    · rw [mem_boxDoubled]; exact ⟨K, hK𝒜, L, hLℬ, hKL, rfl⟩
    · rw [Finset.union_subset_iff]; exact ⟨hKS, hLS⟩
  · rintro ⟨U, hU, K, L, rfl, hKL⟩
    rw [mem_boxDoubled] at hU
    obtain ⟨K', hK'𝒜, L', hL'ℬ, hdisj, hdbl⟩ := hU
    
    have hpair : (K', L') = (K, L) := dbl_injective (by simpa using hdbl)
    rw [Prod.mk.injEq] at hpair
    obtain ⟨hKeq, hLeq⟩ := hpair
    subst hKeq; subst hLeq
    rw [Finset.union_subset_iff] at hKL
    exact ⟨K', L', hdisj, hKL.1, hKL.2, hK'𝒜, hL'ℬ⟩

open Classical in





theorem rc11_boxSupp_iff_collapse (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc10_boxSupp 𝒜 ℬ ↔
      ∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S := by
  rw [rc10_boxSupp, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨K, L, hKL, hKS, hLS, hK𝒜, hLℬ⟩
    refine ⟨dbl K L, ?_, ?_⟩
    · rw [mem_boxDoubled]; exact ⟨K, hK𝒜, L, hLℬ, hKL, rfl⟩
    · rw [image_collapse_dbl, Finset.union_subset_iff]; exact ⟨hKS, hLS⟩
  · rintro ⟨U, hU, hsub⟩
    rw [mem_boxDoubled] at hU
    obtain ⟨K, hK𝒜, L, hLℬ, hdisj, hdbl⟩ := hU
    subst hdbl
    rw [image_collapse_dbl, Finset.union_subset_iff] at hsub
    exact ⟨K, L, hdisj, hsub.1, hsub.2, hK𝒜, hLℬ⟩

set_option linter.unusedFintypeInType false in




theorem rc11_boxSupp_doubled_iff_collapse (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    (∃ U ∈ boxDoubled 𝒜 ℬ, ∃ K L : Finset α, U = dbl K L ∧ K ∪ L ⊆ S) ↔
      (∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S) := by
  rw [← rc11_boxSupp_iff_doubled, ← rc11_boxSupp_iff_collapse]







open Classical in



theorem rc11_empty_mem_boxSupp_univ :
    (∅ : Finset (Fin 2)) ∈ rc10_boxSupp (univ : Finset (Finset (Fin 2))) univ := by
  rw [rc11_boxSupp_iff_doubled]
  refine ⟨dbl ∅ ∅, ?_, ∅, ∅, rfl, ?_⟩
  · rw [mem_boxDoubled]; exact ⟨∅, mem_univ _, ∅, mem_univ _, disjoint_empty_left _, rfl⟩
  · simp







open Classical in










theorem rc11_double_cover_representation (𝒜 ℬ : Finset (Finset α)) :
    (∀ S : Finset α, S ∈ rc10_boxSupp 𝒜 ℬ ↔
        ∃ U ∈ boxDoubled 𝒜 ℬ, ∃ K L : Finset α, U = dbl K L ∧ K ∪ L ⊆ S)
      ∧ (∀ S : Finset α, S ∈ rc10_boxSupp 𝒜 ℬ ↔
          ∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S)
      ∧ ((boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card)
      ∧ IsUpperSet ((rc10_boxSupp 𝒜 ℬ) : Set (Finset α)) :=
  ⟨rc11_boxSupp_iff_doubled 𝒜 ℬ, rc11_boxSupp_iff_collapse 𝒜 ℬ,
    rc11_card_boxDoubled 𝒜 ℬ, rc11_isUpperSet_boxSupp 𝒜 ℬ⟩

end StatMech.Walls
