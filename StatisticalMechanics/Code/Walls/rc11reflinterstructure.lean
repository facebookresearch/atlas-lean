/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Code.Walls.rc10core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]



open Classical in





noncomputable def rc11_reflPull (ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => Sᶜ ∈ ℬ)

open Classical in

theorem rc11_mem_reflPull (ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc11_reflPull ℬ ↔ Sᶜ ∈ ℬ := by
  simp [rc11_reflPull]



open Classical in







theorem rc11_isLowerSet_reflPull {ℬ : Finset (Finset α)}
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    IsLowerSet ((rc11_reflPull ℬ : Finset (Finset α)) : Set (Finset α)) := by
  intro S T hTS hS
  
  simp only [Finset.mem_coe, rc11_mem_reflPull] at hS ⊢
  
  exact hℬ (compl_le_compl hTS) hS

open Classical in




theorem rc11_isUpperSet_of_isLowerSet_reflPull {ℬ : Finset (Finset α)}
    (h : IsLowerSet ((rc11_reflPull ℬ : Finset (Finset α)) : Set (Finset α))) :
    IsUpperSet (ℬ : Set (Finset α)) := by
  intro S T hST hS
  
  
  
  have hSc : Sᶜ ∈ rc11_reflPull ℬ := by rw [rc11_mem_reflPull, compl_compl]; exact hS
  have hTc : Tᶜ ∈ rc11_reflPull ℬ := by
    have := h (a := Sᶜ) (b := Tᶜ) (compl_le_compl hST) (by simpa using hSc)
    simpa using this
  rw [rc11_mem_reflPull, compl_compl] at hTc
  exact hTc



open Classical in


theorem rc11_reflInter_eq_inter (𝒜 ℬ : Finset (Finset α)) :
    rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc11_reflPull ℬ := by
  ext S
  simp only [rc10_reflInter, rc11_reflPull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]



open Classical in








theorem rc11_reflInter_isUpperMeetDown {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    ∃ rℬ : Finset (Finset α),
      IsUpperSet (𝒜 : Set (Finset α)) ∧ IsLowerSet (rℬ : Set (Finset α)) ∧
        rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rℬ :=
  ⟨rc11_reflPull ℬ, h𝒜, rc11_isLowerSet_reflPull hℬ, rc11_reflInter_eq_inter 𝒜 ℬ⟩



open Classical in


theorem rc11_reflPull_reflPull (ℬ : Finset (Finset α)) :
    rc11_reflPull (rc11_reflPull ℬ) = ℬ := by
  ext S
  rw [rc11_mem_reflPull, rc11_mem_reflPull, compl_compl]

open Classical in



theorem rc11_reflPull_univ :
    rc11_reflPull (univ : Finset (Finset α)) = univ := by
  ext S; rw [rc11_mem_reflPull]; simp

open Classical in



theorem rc11_reflInter_univ_univ :
    rc10_reflInter (univ : Finset (Finset α)) univ = univ := by
  rw [rc11_reflInter_eq_inter, rc11_reflPull_univ, Finset.inter_self]









open Classical in




theorem rc11_card_reflInter_eq_card_upperMeetDown {𝒜 ℬ : Finset (Finset α)}
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #(rc10_reflInter 𝒜 ℬ) = #(𝒜 ∩ rc11_reflPull ℬ)
      ∧ IsLowerSet ((rc11_reflPull ℬ : Finset (Finset α)) : Set (Finset α)) :=
  ⟨by rw [rc11_reflInter_eq_inter], rc11_isLowerSet_reflPull hℬ⟩

end StatMech.Walls
