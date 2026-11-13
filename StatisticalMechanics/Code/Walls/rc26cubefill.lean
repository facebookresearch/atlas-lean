/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Code.Walls.rc25doubledcover
import Code.Walls.rc23boxmono

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









open Classical in



theorem rc26_famCylBox_subset_left (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, _, _, hKA, _⟩ := hS
  exact hKA S rfl

open Classical in


theorem rc26_famCylBox_subset_right (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ ℬ := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨_, L, _, _, hLB⟩ := hS
  exact hLB S rfl

open Classical in




theorem rc26_famCylBox_subset_inter (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ := by
  intro S hS
  rw [Finset.mem_inter]
  exact ⟨rc26_famCylBox_subset_left 𝒜 ℬ hS, rc26_famCylBox_subset_right 𝒜 ℬ hS⟩






open Classical in


theorem rc26_reflInter_subset_left (𝒜 ℬ : Finset (Finset α)) :
    rc10_reflInter 𝒜 ℬ ⊆ 𝒜 := by
  intro S hS
  rw [rc20_mem_reflInter] at hS
  exact hS.1











open Classical in



theorem rc26_both_subset_left (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∧ rc10_reflInter 𝒜 ℬ ⊆ 𝒜 :=
  ⟨rc26_famCylBox_subset_left 𝒜 ℬ, rc26_reflInter_subset_left 𝒜 ℬ⟩












set_option maxRecDepth 10000 in




theorem rc26_box_not_subset_reflInter :
    ¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}})
        ⊆ rc10_reflInter ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}})) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]
  decide


















set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
open Classical in







theorem rc26_singleCover_routes_dead :
    rc22_BoxDownsetBase
      ∧ (¬ rc22_BoxCompressionMono)
      ∧ (¬ rc24_BoxDownUpMono)
      ∧ (∀ [Fintype α] (i : α) (𝒜 ℬ : Finset (Finset α)),
          #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
            ≤ #(rc10_reflInter 𝒜 ℬ)) :=
  ⟨rc23_boxDownsetBase, rc23_boxCompressionMono_false, rc25_boxDownUpMono_false,
    fun i 𝒜 ℬ => rc22_reflInter_downDown_antitone i 𝒜 ℬ⟩








open Classical in




theorem rc26_cylBoxReflInter_of_boxDoubledCount (h : rc25_BoxDoubledCount) :
    rc18_CylBoxReflInter :=
  rc25_cylBoxReflInter_of_boxDoubledCount h

open Classical in





theorem rc26_boxDoubledCount_iff_reflInter :
    rc25_BoxDoubledCount ↔
      ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  constructor
  · intro h n 𝒜 ℬ
    rw [rc22_card_reflInter_eq_complPairs]; exact h n 𝒜 ℬ
  · intro h n 𝒜 ℬ
    rw [← rc22_card_reflInter_eq_complPairs]; exact h n 𝒜 ℬ















theorem rc26_boxDoubledCount_strict_witness :
    #(rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 3)))
        ({∅, {1}, {2}, {1,2}, {0,1,2}}))
      < #(rc22_complPairs ({∅, {0}} : Finset (Finset (Fin 3)))
        ({∅, {1}, {2}, {1,2}, {0,1,2}})) := by
  rw [← rc22_card_reflInter_eq_complPairs, ← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]
  decide

open Classical in



theorem rc26_boxDoubledCount_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc22_complPairs 𝒜 ℬ) :=
  rc25_boxDoubledCount_fin2 𝒜 ℬ



set_option linter.unusedSectionVars false in
open Classical in





























theorem rc26_reimer_cubefill :
    (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc10_reflInter 𝒜 ℬ ⊆ 𝒜)
      ∧ (¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}})
          ⊆ rc10_reflInter ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}})))
      ∧ (¬ rc22_BoxCompressionMono)
      ∧ (¬ rc24_BoxDownUpMono)
      ∧ rc22_BoxDownsetBase
      ∧ (rc25_BoxDoubledCount ↔
          ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
            #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc25_BoxDoubledCount → rc18_CylBoxReflInter) :=
  ⟨rc26_famCylBox_subset_inter,
    rc26_reflInter_subset_left,
    rc26_box_not_subset_reflInter,
    rc23_boxCompressionMono_false,
    rc25_boxDownUpMono_false,
    rc23_boxDownsetBase,
    rc26_boxDoubledCount_iff_reflInter,
    rc26_cylBoxReflInter_of_boxDoubledCount⟩

end StatMech.Walls
