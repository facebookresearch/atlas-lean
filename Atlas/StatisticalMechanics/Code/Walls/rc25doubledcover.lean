/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Code.Walls.rc24countbridge
import Code.Inequalities.ReimerButterflyStep

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]

















set_option maxRecDepth 100000 in

set_option maxHeartbeats 40000000 in







theorem rc25_boxDownUp_strictDecrease :
    #(rc20_famCylBox
        (Down.compression 0 ({∅, {0}, {1}, {2}, {0,1}, {0,2}} : Finset (Finset (Fin 3))))
        (rc22_upComp 0 ({∅, {0}, {2}, {0,1}} : Finset (Finset (Fin 3)))))
      < #(rc20_famCylBox ({∅, {0}, {1}, {2}, {0,1}, {0,2}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {2}, {0,1}})) := by
  rw [← rc24_upCompComp_eq, ← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  decide









theorem rc25_boxDownUpMono_false : ¬ rc24_BoxDownUpMono := by
  intro h
  have hle := h 3 ({∅, {0}, {1}, {2}, {0,1}, {0,2}})
    ({∅, {0}, {2}, {0,1}}) 0
  exact absurd hle (not_le.mpr rc25_boxDownUp_strictDecrease)

















open Classical in



noncomputable def rc25_witness (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Finset α :=
  if h : S ∈ rc24_complCylBox 𝒜 ℬ then Classical.choose ((rc24_mem_complCylBox 𝒜 ℬ S).mp h) else ∅

open Classical in







theorem rc25_box_le_dpairs (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ := by
  rw [rc24_famCylBox_eq_complCylBox, dpairsCount]
  apply Finset.card_le_card_of_injOn
    (fun S => (S ∩ rc25_witness 𝒜 ℬ S, S ∩ (rc25_witness 𝒜 ℬ S)ᶜ))
  · intro S hS
    simp only [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    dsimp only
    have hmem := (rc24_mem_complCylBox 𝒜 ℬ S).mp hS
    have hspec := Classical.choose_spec ((rc24_mem_complCylBox 𝒜 ℬ S).mp hS)
    have hw : rc25_witness 𝒜 ℬ S = Classical.choose hmem := by
      rw [rc25_witness]; rw [dif_pos hS]
    rw [hw]
    obtain ⟨hKA, hKcB⟩ := hspec
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hKA (S ∩ Classical.choose hmem) (by rw [Finset.inter_assoc, Finset.inter_self])
    · exact hKcB (S ∩ (Classical.choose hmem)ᶜ) (by rw [Finset.inter_assoc, Finset.inter_self])
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right disjoint_compl_right)
  · intro S _ S' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have eS : S ∩ rc25_witness 𝒜 ℬ S ∪ S ∩ (rc25_witness 𝒜 ℬ S)ᶜ = S := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have eS' : S' ∩ rc25_witness 𝒜 ℬ S' ∪ S' ∩ (rc25_witness 𝒜 ℬ S')ᶜ = S' := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← eS, ← eS', h1, h2]














open Classical in






theorem rc25_witness_partition (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    (S ∩ rc25_witness 𝒜 ℬ S) ∪ (S ∩ (rc25_witness 𝒜 ℬ S)ᶜ) = S := by
  rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]














open Classical in





def rc25_BoxDoubledCount : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc22_complPairs 𝒜 ℬ)

open Classical in





theorem rc25_boxDoubledCount_iff_famCylBoxResidue :
    rc25_BoxDoubledCount ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    rw [rc22_card_reflInter_eq_complPairs]; exact h n 𝒜 ℬ
  · intro h n 𝒜 ℬ
    rw [← rc22_card_reflInter_eq_complPairs]; exact h n 𝒜 ℬ




theorem rc25_cylBoxReflInter_of_boxDoubledCount (h : rc25_BoxDoubledCount) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp
    (rc25_boxDoubledCount_iff_famCylBoxResidue.mp h)








open Classical in



theorem rc25_boxDoubledCount_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc22_complPairs 𝒜 ℬ) := by
  rw [← rc22_card_reflInter_eq_complPairs]
  exact rc20_famCylBox_fin2 𝒜 ℬ






theorem rc25_boxDoubledCount_strict_witness :
    #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {1}, {2}, {0,2}, {1,2}}))
      < #(rc22_complPairs ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {1}, {2}, {0,2}, {1,2}})) := by
  rw [← rc22_card_reflInter_eq_complPairs, ← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]
  decide



open Classical in


























theorem rc25_reimer_doubledcover :
    (¬ rc24_BoxDownUpMono)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), #(rc20_famCylBox 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)) (S : Finset α),
          (S ∩ rc25_witness 𝒜 ℬ S) ∪ (S ∩ (rc25_witness 𝒜 ℬ S)ᶜ) = S)
      ∧ (rc25_BoxDoubledCount ↔ rc20_FamCylBoxResidue)
      ∧ (rc25_BoxDoubledCount → rc18_CylBoxReflInter) :=
  ⟨rc25_boxDownUpMono_false,
    rc25_box_le_dpairs,
    rc25_witness_partition,
    rc25_boxDoubledCount_iff_famCylBoxResidue,
    rc25_cylBoxReflInter_of_boxDoubledCount⟩

end StatMech.Walls
