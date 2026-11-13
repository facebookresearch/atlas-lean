/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Code.Walls.rc10core

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








open Classical in


theorem rc11_mem_boxSupp (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc10_boxSupp 𝒜 ℬ ↔
      ∃ K L : Finset α, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S ∧ K ∈ 𝒜 ∧ L ∈ ℬ := by
  simp only [rc10_boxSupp, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in




theorem rc11_boxSupp_mem_of_subset (𝒜 ℬ : Finset (Finset α)) {S S' : Finset α} (hSS' : S ⊆ S')
    (hS : S ∈ rc10_boxSupp 𝒜 ℬ) : S' ∈ rc10_boxSupp 𝒜 ℬ := by
  rw [rc11_mem_boxSupp] at hS ⊢
  obtain ⟨K, L, hKL, hKS, hLS, hKA, hLB⟩ := hS
  exact ⟨K, L, hKL, hKS.trans hSS', hLS.trans hSS', hKA, hLB⟩



open Classical in





theorem rc11_isUpperSet_boxSupp (𝒜 ℬ : Finset (Finset α)) :
    IsUpperSet ((rc10_boxSupp 𝒜 ℬ : Finset (Finset α)) : Set (Finset α)) := by
  intro S S' hSS' hS
  simp only [Finset.mem_coe] at hS ⊢
  exact rc11_boxSupp_mem_of_subset 𝒜 ℬ (le_iff_subset.mp hSS') hS

open Classical in





theorem rc11_boxSupp_upper (𝒜 ℬ : Finset (Finset α))
    (_h𝒜 : IsUpperSet ((𝒜 : Finset (Finset α)) : Set (Finset α)))
    (_hℬ : IsUpperSet ((ℬ : Finset (Finset α)) : Set (Finset α))) :
    IsUpperSet ((rc10_boxSupp 𝒜 ℬ : Finset (Finset α)) : Set (Finset α)) :=
  rc11_isUpperSet_boxSupp 𝒜 ℬ









open Classical in

theorem rc11_mem_reflInter (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc10_reflInter 𝒜 ℬ ↔ S ∈ 𝒜 ∧ Sᶜ ∈ ℬ := by
  simp only [rc10_reflInter, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in






theorem rc11_reflInter_clause_antitone {S S' : Finset α} (hSS' : S ⊆ S') :
    S'ᶜ ⊆ Sᶜ :=
  Finset.compl_subset_compl.mpr hSS'







open Classical in


theorem rc11_isUpperSet_boxSupp_univ :
    IsUpperSet ((rc10_boxSupp (univ : Finset (Finset α)) univ : Finset (Finset α))
      : Set (Finset α)) :=
  rc11_isUpperSet_boxSupp univ univ










theorem rc11_boxsupp_upper_node :
    (∀ 𝒜 ℬ : Finset (Finset α),
        IsUpperSet ((rc10_boxSupp 𝒜 ℬ : Finset (Finset α)) : Set (Finset α)))
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)) {S S' : Finset α}, S ⊆ S' →
          S ∈ rc10_boxSupp 𝒜 ℬ → S' ∈ rc10_boxSupp 𝒜 ℬ) :=
  ⟨rc11_isUpperSet_boxSupp, fun 𝒜 ℬ _ _ hSS' hS => rc11_boxSupp_mem_of_subset 𝒜 ℬ hSS' hS⟩

end StatMech.Walls
