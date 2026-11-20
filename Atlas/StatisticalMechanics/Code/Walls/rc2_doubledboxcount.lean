/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Code.Inequalities.ReimerButterflyStep

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]








def rc2_disjointPairs (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α × Finset α) :=
  (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)

@[simp] lemma rc2_mem_disjointPairs {𝒜 ℬ : Finset (Finset α)} {p : Finset α × Finset α} :
    p ∈ rc2_disjointPairs 𝒜 ℬ ↔ (p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ) ∧ Disjoint p.1 p.2 := by
  simp only [rc2_disjointPairs, mem_filter, mem_product]



theorem rc2_dpairsCount_eq_card_disjointPairs (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = (rc2_disjointPairs 𝒜 ℬ).card := rfl













theorem rc2_dbl_injOn_disjointPairs (𝒜 ℬ : Finset (Finset α)) :
    Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) (rc2_disjointPairs 𝒜 ℬ) :=
  dbl_injective.injOn



theorem rc2_boxDoubled_eq_image (𝒜 ℬ : Finset (Finset α)) :
    boxDoubled 𝒜 ℬ = (rc2_disjointPairs 𝒜 ℬ).image (fun p => dbl p.1 p.2) := rfl








theorem rc2_card_boxDoubled_eq_card_disjointPairs (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = (rc2_disjointPairs 𝒜 ℬ).card := by
  rw [rc2_boxDoubled_eq_image, Finset.card_image_of_injOn (rc2_dbl_injOn_disjointPairs 𝒜 ℬ)]












theorem rc2_doubled_box_count (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
  rw [rc2_card_boxDoubled_eq_card_disjointPairs, rc2_dpairsCount_eq_card_disjointPairs]



theorem rc2_doubled_box_count_chain (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ ∧
      dpairsCount 𝒜 ℬ = (rc2_disjointPairs 𝒜 ℬ).card :=
  ⟨rc2_doubled_box_count 𝒜 ℬ, rc2_dpairsCount_eq_card_disjointPairs 𝒜 ℬ⟩











theorem rc2_union_not_injOn_disjointPairs (a : α) :
    ¬ Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2)
        (rc2_disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}}) := by
  intro hinj
  have hp1 : (({a}, ∅) : Finset α × Finset α) ∈
      rc2_disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}} := by
    rw [rc2_mem_disjointPairs]
    exact ⟨⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      Finset.mem_insert_self _ _⟩, by simp⟩
  have hp2 : ((∅, {a}) : Finset α × Finset α) ∈
      rc2_disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}} := by
    rw [rc2_mem_disjointPairs]
    exact ⟨⟨Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, by simp⟩
  have hunion : (({a}, ∅) : Finset α × Finset α).1 ∪ (({a}, ∅) : Finset α × Finset α).2
      = ((∅, {a}) : Finset α × Finset α).1 ∪ ((∅, {a}) : Finset α × Finset α).2 := by simp
  have heq := hinj hp1 hp2 hunion
  have hne : (({a}, ∅) : Finset α × Finset α) ≠ ((∅, {a}) : Finset α × Finset α) := by
    intro h
    exact (Finset.singleton_ne_empty a) (congrArg Prod.fst h)
  exact hne heq










def rc2_collapseFamily : Finset (Finset (Fin 2)) := {∅, {1}}


theorem rc2_collapse_dpairsCount :
    dpairsCount rc2_collapseFamily rc2_collapseFamily = 3 := by decide



theorem rc2_collapse_boxDoubled :
    (boxDoubled rc2_collapseFamily rc2_collapseFamily).card = 3 := by
  rw [rc2_doubled_box_count]; exact rc2_collapse_dpairsCount



theorem rc2_collapse_boxFamily :
    (boxFamily rc2_collapseFamily rc2_collapseFamily).card = 2 := by decide







theorem rc2_collapse_witness :
    (boxFamily rc2_collapseFamily rc2_collapseFamily).card
        < dpairsCount rc2_collapseFamily rc2_collapseFamily ∧
      dpairsCount rc2_collapseFamily rc2_collapseFamily
        = (boxDoubled rc2_collapseFamily rc2_collapseFamily).card := by
  refine ⟨?_, ?_⟩
  · rw [rc2_collapse_boxFamily, rc2_collapse_dpairsCount]; norm_num
  · rw [rc2_collapse_dpairsCount, rc2_collapse_boxDoubled]




theorem rc2_dpairsCount_empty_left (ℬ : Finset (Finset α)) :
    dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
  rw [rc2_dpairsCount_eq_card_disjointPairs]
  simp [rc2_disjointPairs]


theorem rc2_doubled_box_count_empty_left (ℬ : Finset (Finset α)) :
    (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
  rw [rc2_doubled_box_count, rc2_dpairsCount_empty_left]

end StatMech.Walls
