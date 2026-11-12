/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Code.Inequalities.ReimerButterflyProve3

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]









omit [DecidableEq α] in



theorem rc6_totalSize_eq_sum (𝒜 : Finset (Finset α)) :
    totalSize 𝒜 = ∑ S ∈ 𝒜, S.card :=
  rfl




theorem rc6_totalSize_nonincreasing (i : α) (𝒜 : Finset (Finset α)) :
    totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜 :=
  totalSize_downComp_le i 𝒜







theorem rc6_totalSize_strictly_drops (i : α) (𝒜 : Finset (Finset α))
    (hne : Down.compression i 𝒜 ≠ 𝒜) :
    totalSize (Down.compression i 𝒜) < totalSize 𝒜 :=
  totalSize_downComp_lt i 𝒜 hne
















theorem rc6_isLowerSet_iff_fixedByAll (𝒜 : Finset (Finset α)) :
    IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i : α, Down.compression i 𝒜 = 𝒜 :=
  isLowerSet_iff_forall_downComp_eq_self 𝒜




theorem rc6_exists_nonfixpoint_of_not_isLowerSet {𝒜 : Finset (Finset α)}
    (h : ¬ IsLowerSet (𝒜 : Set (Finset α))) :
    ∃ i : α, totalSize (Down.compression i 𝒜) < totalSize 𝒜 := by
  rw [rc6_isLowerSet_iff_fixedByAll, not_forall] at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, rc6_totalSize_strictly_drops i 𝒜 hi⟩
















theorem rc6_sweep_reaches_downset (𝒜 : Finset (Finset α)) :
    ∃ cs : List α,
      IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
        ∧ (iterDownComp cs 𝒜).card = 𝒜.card := by
  obtain ⟨cs, hcs⟩ := exists_iterDownComp_isLowerSet 𝒜
  exact ⟨cs, hcs, iterDownComp_card cs 𝒜⟩





















theorem rc6_blMonovariant :
    (∀ (i : α) (𝒜 : Finset (Finset α)), Down.compression i 𝒜 ≠ 𝒜 →
        totalSize (Down.compression i 𝒜) < totalSize 𝒜)
      ∧ (∀ (i : α) (𝒜 : Finset (Finset α)),
          totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜)
      ∧ (∀ 𝒜 : Finset (Finset α),
          IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i : α, Down.compression i 𝒜 = 𝒜)
      ∧ (∀ 𝒜 : Finset (Finset α), ∃ cs : List α,
          IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
            ∧ (iterDownComp cs 𝒜).card = 𝒜.card) :=
  ⟨fun i 𝒜 hne => rc6_totalSize_strictly_drops i 𝒜 hne,
    fun i 𝒜 => rc6_totalSize_nonincreasing i 𝒜,
    fun 𝒜 => rc6_isLowerSet_iff_fixedByAll 𝒜,
    fun 𝒜 => rc6_sweep_reaches_downset 𝒜⟩










theorem rc6_blMonovariant_assembly (𝒜 : Finset (Finset α)) :
    
    (∀ (i : α) (ℬ : Finset (Finset α)), Down.compression i ℬ ≠ ℬ →
        totalSize (Down.compression i ℬ) < totalSize ℬ)
      ∧ (∀ ℬ : Finset (Finset α),
          IsLowerSet (ℬ : Set (Finset α)) ↔ ∀ i : α, Down.compression i ℬ = ℬ)
      
      ∧ (∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
          ∧ (iterDownComp cs 𝒜).card = 𝒜.card) :=
  ⟨fun i ℬ hne => rc6_totalSize_strictly_drops i ℬ hne,
    fun ℬ => rc6_isLowerSet_iff_fixedByAll ℬ,
    rc6_sweep_reaches_downset 𝒜⟩









theorem rc6_sweep_isLowerSet_self {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet ((iterDownComp ([] : List α) 𝒜) : Set (Finset α))
      ∧ (iterDownComp ([] : List α) 𝒜).card = 𝒜.card := by
  rw [iterDownComp_nil]
  exact ⟨h, rfl⟩

omit [DecidableEq α] in



theorem rc6_univ_isLowerSet [Fintype α] :
    IsLowerSet ((Finset.univ : Finset (Finset α)) : Set (Finset α)) := by
  intro s t _ _
  simp





theorem rc6_strict_drop_singleton (a : α) :
    totalSize (Down.compression a ({{a}} : Finset (Finset α)))
      < totalSize ({{a}} : Finset (Finset α)) := by
  apply rc6_totalSize_strictly_drops
  
  intro hfix
  have hmem : (∅ : Finset α) ∈ Down.compression a ({{a}} : Finset (Finset α)) := by
    rw [Down.mem_compression]
    refine Or.inr ⟨?_, ?_⟩
    · simp
    · exact Finset.mem_singleton.mpr rfl
  rw [hfix] at hmem
  simp at hmem

end StatMech.Walls
