/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Code.Walls.rc15dimreduce

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







open Classical in

theorem rc16_boxE_left_subset {E : Finset α} {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    rc14_boxE E 𝒜 ℬ ⊆ rc14_boxE E 𝒜' ℬ := by
  intro S hS
  rw [rc14_mem_boxE] at hS ⊢
  obtain ⟨hSE, K, L, hKL, hKS, hLS, hK, hL⟩ := hS
  exact ⟨hSE, K, L, hKL, hKS, hLS, h hK, hL⟩

open Classical in

theorem rc16_boxE_right_subset {E : Finset α} {𝒜 ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    rc14_boxE E 𝒜 ℬ ⊆ rc14_boxE E 𝒜 ℬ' := by
  intro S hS
  rw [rc14_mem_boxE] at hS ⊢
  obtain ⟨hSE, K, L, hKL, hKS, hLS, hK, hL⟩ := hS
  exact ⟨hSE, K, L, hKL, hKS, hLS, hK, h hL⟩













open Classical in



theorem rc16_boxE_nonMem_subset_mem_left {E : Finset α} {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : rc15_UpperOn E 𝒜) (a : α) (haE : a ∈ E) :
    rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) ℬ
      ⊆ rc14_boxE (E.erase a) (𝒜.memberSubfamily a) ℬ := by
  intro S hS
  rw [rc14_mem_boxE] at hS ⊢
  obtain ⟨hSF, K, L, hKL, hKS, hLS, hK, hL⟩ := hS
  rw [mem_nonMemberSubfamily] at hK
  obtain ⟨hK𝒜, haK⟩ := hK
  refine ⟨hSF, K, L, hKL, hKS, hLS, ?_, hL⟩
  
  exact rc15_mem_member_of_nonMem h𝒜 a haE
    ((hKS.trans hSF).trans (Finset.erase_subset a E)) haK hK𝒜

open Classical in



theorem rc16_boxE_nonMem_subset_mem_right {E : Finset α} {𝒜 ℬ : Finset (Finset α)}
    (hℬ : rc15_UpperOn E ℬ) (a : α) (haE : a ∈ E) :
    rc14_boxE (E.erase a) 𝒜 (ℬ.nonMemberSubfamily a)
      ⊆ rc14_boxE (E.erase a) 𝒜 (ℬ.memberSubfamily a) := by
  intro S hS
  rw [rc14_mem_boxE] at hS ⊢
  obtain ⟨hSF, K, L, hKL, hKS, hLS, hK, hL⟩ := hS
  rw [mem_nonMemberSubfamily] at hL
  obtain ⟨hLℬ, haL⟩ := hL
  refine ⟨hSF, K, L, hKL, hKS, hLS, hK, ?_⟩
  exact rc15_mem_member_of_nonMem hℬ a haE
    ((hLS.trans hSF).trans (Finset.erase_subset a E)) haL hLℬ

open Classical in




theorem rc16_boxE_base_subset_inter {E : Finset α} {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : rc15_UpperOn E 𝒜) (hℬ : rc15_UpperOn E ℬ) (a : α) (haE : a ∈ E) :
    rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)
      ⊆ rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)
          ∩ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a) := by
  rw [Finset.subset_inter_iff]
  exact ⟨rc16_boxE_nonMem_subset_mem_left h𝒜 a haE,
    rc16_boxE_nonMem_subset_mem_right hℬ a haE⟩






open Classical in











theorem rc16_bkrground_step {E : Finset α} {a : α} (haE : a ∈ E)
    (hIH : rc15_BKRground (E.erase a)) : rc15_BKRground E := by
  intro 𝒜 ℬ h𝒜 hℬ
  rw [rc15_card_boxE_slice h𝒜 a haE, rc15_card_reflE_slice E 𝒜 ℬ a haE]
  set F := E.erase a with hF
  set 𝒜₀ := 𝒜.nonMemberSubfamily a with h𝒜₀
  set 𝒜₁ := 𝒜.memberSubfamily a with h𝒜₁
  set ℬ₀ := ℬ.nonMemberSubfamily a with hℬ₀
  set ℬ₁ := ℬ.memberSubfamily a with hℬ₁
  
  have hIH10 : #(rc14_boxE F 𝒜₁ ℬ₀) ≤ #(rc14_reflE F 𝒜₁ ℬ₀) :=
    hIH 𝒜₁ ℬ₀ (rc15_upperOn_member h𝒜 a haE) (rc15_upperOn_nonMember hℬ a)
  have hIH01 : #(rc14_boxE F 𝒜₀ ℬ₁) ≤ #(rc14_reflE F 𝒜₀ ℬ₁) :=
    hIH 𝒜₀ ℬ₁ (rc15_upperOn_nonMember h𝒜 a) (rc15_upperOn_member hℬ a haE)
  
  have hbase : #(rc14_boxE F 𝒜₀ ℬ₀)
      ≤ #(rc14_boxE F 𝒜₁ ℬ₀ ∩ rc14_boxE F 𝒜₀ ℬ₁) :=
    Finset.card_le_card (rc16_boxE_base_subset_inter h𝒜 hℬ a haE)
  
  have hIE : #(rc14_boxE F 𝒜₁ ℬ₀ ∪ rc14_boxE F 𝒜₀ ℬ₁)
      + #(rc14_boxE F 𝒜₁ ℬ₀ ∩ rc14_boxE F 𝒜₀ ℬ₁)
      = #(rc14_boxE F 𝒜₁ ℬ₀) + #(rc14_boxE F 𝒜₀ ℬ₁) :=
    Finset.card_union_add_card_inter _ _
  
  
  omega







open Classical in




theorem rc16_bkrground : ∀ E : Finset α, rc15_BKRground E := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    rcases E.eq_empty_or_nonempty with rfl | ⟨a, haE⟩
    · exact rc15_bkrground_empty
    · exact rc16_bkrground_step haE (ih (E.erase a) (Finset.erase_ssubset haE))



open Classical in










theorem rc16_bkrSetFamily : rc10_BKRSetFamily :=
  rc15_bkrSetFamily_of_bkrground (fun β _ _ => rc16_bkrground (univ : Finset β))










theorem rc16_bkrInjectionAll : rc11_BKRInjectionAll :=
  rc11_injectionAll_of_bkr rc16_bkrSetFamily




theorem rc16_deficitBridgeIncInc : rc10_DeficitBridgeIncInc :=
  rc10_deficitIncInc_of_bkr rc16_bkrSetFamily

end StatMech.Walls
