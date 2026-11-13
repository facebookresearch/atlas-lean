/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Code.Walls.rc48cover
import Code.Inequalities.ReimerDoubled
import Mathlib.Combinatorics.Hall.Basic

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]














def rc49_jointImage (S K L : Finset α) : Finset α :=
  (S ∩ K) ∪ (L ∩ Sᶜ) ∪ (S ∩ (K ∪ L)ᶜ)




theorem rc49_jointImage_inter_K (S K L : Finset α) (hKL : Disjoint K L) :
    rc49_jointImage S K L ∩ K = S ∩ K := by
  rw [rc49_jointImage]
  ext a
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
  constructor
  · rintro ⟨(⟨_, _⟩ | ⟨haL, _⟩) | ⟨_, haKL⟩, haK⟩
    · exact ⟨‹a ∈ S›, haK⟩
    · exact absurd haK (Finset.disjoint_right.mp hKL haL)
    · exact absurd (Or.inl haK) haKL
  · rintro ⟨haS, haK⟩
    exact ⟨Or.inl (Or.inl ⟨haS, haK⟩), haK⟩




theorem rc49_jointImage_compl_inter_L (S K L : Finset α) (hKL : Disjoint K L) :
    (rc49_jointImage S K L)ᶜ ∩ L = S ∩ L := by
  rw [rc49_jointImage]
  ext a
  constructor
  · intro ha
    rw [Finset.mem_inter, Finset.mem_compl] at ha
    obtain ⟨hnot, haL⟩ := ha
    rw [Finset.mem_inter]
    refine ⟨?_, haL⟩
    by_contra haS
    exact hnot (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_inter.mpr ⟨haL, Finset.mem_compl.mpr haS⟩)))
  · intro ha
    rw [Finset.mem_inter] at ha
    obtain ⟨haS, haL⟩ := ha
    rw [Finset.mem_inter, Finset.mem_compl]
    refine ⟨?_, haL⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · rcases Finset.mem_union.mp h with h1 | h2
      · exact Finset.disjoint_left.mp hKL (Finset.mem_inter.mp h1).2 haL
      · exact (Finset.mem_compl.mp (Finset.mem_inter.mp h2).2) haS
    · exact (Finset.mem_compl.mp (Finset.mem_inter.mp h).2)
        (Finset.mem_union_right _ haL)

open Classical in







theorem rc49_jointImage_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L)
    (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    rc49_jointImage S K L ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter]
  refine ⟨hKA _ (rc49_jointImage_inter_K S K L hKL), hLB _ ?_⟩
  rw [rc49_jointImage_compl_inter_L S K L hKL]








open Classical in



noncomputable def rc49_neighbourhood (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  (rc10_reflInter 𝒜 ℬ).filter (fun R => ∃ K L : Finset α, Disjoint K L ∧
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) ∧
    rc49_jointImage S K L = R)

open Classical in


theorem rc49_neighbourhood_subset_reflInter (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    rc49_neighbourhood 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ :=
  Finset.filter_subset _ _

open Classical in





theorem rc49_neighbourhood_nonempty {𝒜 ℬ : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    (rc49_neighbourhood 𝒜 ℬ S).Nonempty := by
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  refine ⟨rc49_jointImage S K L, ?_⟩
  rw [rc49_neighbourhood, Finset.mem_filter]
  exact ⟨rc49_jointImage_mem_reflInter hKL hKA hLB, K, L, hKL, hKA, hLB, rfl⟩










open Classical in


def rc49_HallCond (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∀ W ⊆ rc20_famCylBox 𝒜 ℬ, #W ≤ #(W.biUnion (rc49_neighbourhood 𝒜 ℬ))

open Classical in






theorem rc49_wall_of_hall (𝒜 ℬ : Finset (Finset α)) (h : rc49_HallCond 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  set box := rc20_famCylBox 𝒜 ℬ with hbox
  
  let t : {S : Finset α // S ∈ box} → Finset (Finset α) :=
    fun S => rc49_neighbourhood 𝒜 ℬ S.1
  have hHall : ∀ s : Finset {S : Finset α // S ∈ box}, #s ≤ #(s.biUnion t) := by
    intro s
    
    have hsub : s.image (Subtype.val) ⊆ box := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, _, rfl⟩ := hx
      exact y.2
    have hcard_s : #s = #(s.image (Subtype.val)) := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
    have hbiU : (s.image (Subtype.val)).biUnion (rc49_neighbourhood 𝒜 ℬ) = s.biUnion t := by
      ext R
      simp only [Finset.mem_biUnion, Finset.mem_image, t]
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, hR⟩; exact ⟨y, hy, hR⟩
      · rintro ⟨y, hy, hR⟩; exact ⟨y.1, ⟨y, hy, rfl⟩, hR⟩
    rw [hcard_s, ← hbiU]
    exact h _ hsub
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  
  calc #box = #(univ : Finset {S : Finset α // S ∈ box}) := by
              rw [Finset.card_univ, Fintype.card_coe]
    _ ≤ #(rc10_reflInter 𝒜 ℬ) := by
              refine Finset.card_le_card_of_injOn f (fun S _ => ?_) (fun a _ b _ hab => hfinj hab)
              exact rc49_neighbourhood_subset_reflInter 𝒜 ℬ S.1 (hfmem S)

open Classical in



def rc49_HallDoubled : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), rc49_HallCond 𝒜 ℬ

open Classical in



theorem rc49_reimer_closes_of_hallDoubled (h : rc49_HallDoubled) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc49_wall_of_hall 𝒜 ℬ (h n 𝒜 ℬ))













set_option maxRecDepth 4000 in



theorem rc49_jointImage_residual_maps_empty_to_zero :
    rc49_jointImage (∅ : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) ({0} : Finset (Fin 3))
      = ({0} : Finset (Fin 3)) := by
  rw [rc49_jointImage]; decide



theorem rc49_residual_KcylA :
    ∀ T : Finset (Fin 3), T ∩ ({1, 2} : Finset (Fin 3)) = (∅ : Finset (Fin 3)) ∩ {1, 2} →
      T ∈ rc48_A₂ := by
  rw [rc48_A₂]; decide




theorem rc49_residual_LcylB :
    ∀ T : Finset (Fin 3), T ∩ ({0} : Finset (Fin 3)) = (∅ : Finset (Fin 3)) ∩ {0} →
      T ∈ rc48_B₂ := by
  rw [rc48_B₂]; decide

open Classical in






theorem rc49_residual_target_mem_reflInter :
    ({0} : Finset (Fin 3)) ∈ rc10_reflInter rc48_A₂ rc48_B₂ := by
  have hd : Disjoint ({1, 2} : Finset (Fin 3)) ({0} : Finset (Fin 3)) := by decide
  have h := rc49_jointImage_mem_reflInter (𝒜 := rc48_A₂) (ℬ := rc48_B₂) (S := (∅ : Finset (Fin 3)))
    hd rc49_residual_KcylA rc49_residual_LcylB
  rwa [rc49_jointImage_residual_maps_empty_to_zero] at h

open Classical in





theorem rc49_residual_neighbourhood_nonempty :
    (rc49_neighbourhood rc48_A₂ rc48_B₂ (∅ : Finset (Fin 3))).Nonempty := by
  refine rc49_neighbourhood_nonempty (𝒜 := rc48_A₂) (ℬ := rc48_B₂) ?_
  rw [rc20_famCylBox, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, {1, 2}, {0}, by decide, rc49_residual_KcylA, rc49_residual_LcylB⟩

set_option maxRecDepth 4000 in




theorem rc49_wall_residual_holds :
    (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card := by
  rw [rc48_A₂, rc48_B₂]; decide



open Classical in





































theorem rc49_reimer_joint_witness :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S K L : Finset (Fin 3)), Disjoint K L →
        (∀ T : Finset (Fin 3), T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ T : Finset (Fin 3), T ∩ L = S ∩ L → T ∈ ℬ) →
        rc49_jointImage S K L ∈ rc10_reflInter 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (S : Finset (Fin 3)),
          S ∈ rc20_famCylBox 𝒜 ℬ → (rc49_neighbourhood 𝒜 ℬ S).Nonempty)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc49_HallCond 𝒜 ℬ →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc49_HallDoubled → rc18_CylBoxReflInter)
      ∧ (rc49_jointImage (∅ : Finset (Fin 3)) ({1, 2}) ({0}) = ({0} : Finset (Fin 3)))
      ∧ (({0} : Finset (Fin 3)) ∈ rc10_reflInter rc48_A₂ rc48_B₂)
      ∧ ((rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card
          ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card) :=
  ⟨fun _ _ _ _ _ hKL hKA hLB => rc49_jointImage_mem_reflInter hKL hKA hLB,
    fun _ _ _ hS => rc49_neighbourhood_nonempty hS,
    fun 𝒜 ℬ h => rc49_wall_of_hall 𝒜 ℬ h,
    rc49_reimer_closes_of_hallDoubled,
    rc49_jointImage_residual_maps_empty_to_zero,
    rc49_residual_target_mem_reflInter,
    rc49_wall_residual_holds⟩

end StatMech.Walls
