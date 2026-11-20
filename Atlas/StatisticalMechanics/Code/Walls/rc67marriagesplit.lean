/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Code.Walls.rc66singletondet

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}









open Classical in


theorem rc67_self_mem_nbhd_of_box_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hbox : S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : S ∈ rc10_reflInter 𝒜 ℬ) :
    S ∈ rc59_nbhd 𝒜 ℬ S :=
  rc66_self_mem_nbhd 𝒜 ℬ hbox hRI

open Classical in



theorem rc67_Tin_self_subset_biUnion (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))}
    (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : ∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) :
    T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
  intro S hS
  have hself : S ∈ rc59_nbhd 𝒜 ℬ S :=
    rc67_self_mem_nbhd_of_box_reflInter 𝒜 ℬ (hbox S hS) (hRI S hS)
  exact Finset.mem_biUnion.mpr ⟨S, hS, hself⟩

open Classical in










theorem rc67_marriage_of_subset_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))}
    (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : ∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) :
    T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  Finset.card_le_card (rc67_Tin_self_subset_biUnion 𝒜 ℬ hbox hRI)













open Classical in

noncomputable def rc67_Tin (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  T ∩ rc10_reflInter 𝒜 ℬ

open Classical in

noncomputable def rc67_Toff (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  T \ rc10_reflInter 𝒜 ℬ

open Classical in


theorem rc67_split_card (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) :
    T.card = (rc67_Tin 𝒜 ℬ T).card + (rc67_Toff 𝒜 ℬ T).card := by
  rw [rc67_Tin, rc67_Toff, Finset.card_inter_add_card_sdiff]

open Classical in


theorem rc67_Tin_subset_biUnion (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    rc67_Tin 𝒜 ℬ T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
  intro S hS
  rw [rc67_Tin, Finset.mem_inter] at hS
  obtain ⟨hST, hSRI⟩ := hS
  have hself : S ∈ rc59_nbhd 𝒜 ℬ S :=
    rc67_self_mem_nbhd_of_box_reflInter 𝒜 ℬ (hbox S hST) hSRI
  exact Finset.mem_biUnion.mpr ⟨S, hST, hself⟩

open Classical in





def rc67_ForcedSelfMatchSDR (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n)))
    (g : Finset (Fin n) → Finset (Fin n)) : Prop :=
  Set.InjOn g (rc67_Toff 𝒜 ℬ T) ∧
    (∀ S ∈ rc67_Toff 𝒜 ℬ T, g S ∈ rc59_nbhd 𝒜 ℬ S) ∧
    (∀ S ∈ rc67_Toff 𝒜 ℬ T, g S ∉ rc67_Tin 𝒜 ℬ T)

open Classical in












theorem rc67_marriage_of_forcedSelfMatch (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
    {g : Finset (Fin n) → Finset (Fin n)} (hg : rc67_ForcedSelfMatchSDR 𝒜 ℬ T g) :
    T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  obtain ⟨hginj, hgnbhd, hgavoid⟩ := hg
  
  set U := rc67_Tin 𝒜 ℬ T ∪ (rc67_Toff 𝒜 ℬ T).image g with hU
  
  have hUsub : U ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
    rw [hU, Finset.union_subset_iff]
    refine ⟨rc67_Tin_subset_biUnion 𝒜 ℬ hbox, ?_⟩
    intro R hR
    rw [Finset.mem_image] at hR
    obtain ⟨S, hS, rfl⟩ := hR
    have hST : S ∈ T := (Finset.mem_sdiff.mp hS).1
    exact Finset.mem_biUnion.mpr ⟨S, hST, hgnbhd S hS⟩
  
  have hdisj : Disjoint (rc67_Tin 𝒜 ℬ T) ((rc67_Toff 𝒜 ℬ T).image g) := by
    rw [Finset.disjoint_left]
    intro R hRin hRimg
    rw [Finset.mem_image] at hRimg
    obtain ⟨S, hS, rfl⟩ := hRimg
    exact hgavoid S hS hRin
  have hcardimg : ((rc67_Toff 𝒜 ℬ T).image g).card = (rc67_Toff 𝒜 ℬ T).card :=
    Finset.card_image_of_injOn hginj
  have hcardU : U.card = T.card := by
    rw [hU, Finset.card_union_of_disjoint hdisj, hcardimg, ← rc67_split_card]
  
  calc T.card = U.card := hcardU.symm
    _ ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := Finset.card_le_card hUsub











open Classical in

theorem rc67_witness_empty_mem_reflInter :
    (∅ : Finset (Fin 2)) ∈ rc10_reflInter rc66_wA rc66_wB := by
  rw [rc20_mem_reflInter]; decide

open Classical in

theorem rc67_witness_empty_mem_Tin :
    (∅ : Finset (Fin 2)) ∈ rc67_Tin rc66_wA rc66_wB {∅, {0}} := by
  rw [rc67_Tin, Finset.mem_inter]
  exact ⟨by simp, rc67_witness_empty_mem_reflInter⟩

open Classical in


theorem rc67_witness_singleton_mem_Toff :
    ({0} : Finset (Fin 2)) ∈ rc67_Toff rc66_wA rc66_wB {∅, {0}} := by
  rw [rc67_Toff, Finset.mem_sdiff]
  exact ⟨by simp, rc66_witness_offReflInter⟩

open Classical in








theorem rc67_forcedSelfMatch_fails_witness :
    ¬ ∃ g : Finset (Fin 2) → Finset (Fin 2),
        rc67_ForcedSelfMatchSDR rc66_wA rc66_wB {∅, {0}} g := by
  rintro ⟨g, _hinj, hgnbhd, hgavoid⟩
  have hToff : ({0} : Finset (Fin 2)) ∈ rc67_Toff rc66_wA rc66_wB {∅, {0}} :=
    rc67_witness_singleton_mem_Toff
  
  have hmem : g {0} ∈ rc59_nbhd rc66_wA rc66_wB {0} := hgnbhd {0} hToff
  rw [rc66_witness_singleton_broken.1, Finset.mem_singleton] at hmem
  
  have hgin : g {0} ∈ rc67_Tin rc66_wA rc66_wB {∅, {0}} := by
    rw [hmem]; exact rc67_witness_empty_mem_Tin
  exact hgavoid {0} hToff hgin








open Classical in




theorem rc67_witness_marriage_holds :
    ({∅, {0}} : Finset (Finset (Fin 2))).card
      ≤ (({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)).card := by
  have hsub : ({∅, {0}} : Finset (Finset (Fin 2))) ⊆ rc20_famCylBox rc66_wA rc66_wB := by
    intro S hS
    rw [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact rc66_witness_box.2.1
    · exact rc66_witness_box.1
  exact rc59_indepHall_fin2 rc66_wA rc66_wB ({∅, {0}}) (Finset.mem_powerset.mpr hsub)



open Classical in

























theorem rc67_status :
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))),
        (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) → (∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) →
        T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))),
        (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) →
        (∃ g : Finset (Fin m) → Finset (Fin m), rc67_ForcedSelfMatchSDR 𝒜 ℬ T g) →
        T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (¬ ∃ g : Finset (Fin 2) → Finset (Fin 2),
        rc67_ForcedSelfMatchSDR rc66_wA rc66_wB {∅, {0}} g) ∧
    
    (({∅, {0}} : Finset (Finset (Fin 2))).card
      ≤ (({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)).card) :=
  ⟨fun _m 𝒜 ℬ _T hbox hRI => rc67_marriage_of_subset_reflInter 𝒜 ℬ hbox hRI,
   fun _m 𝒜 ℬ _T hbox ⟨_g, hg⟩ => rc67_marriage_of_forcedSelfMatch 𝒜 ℬ hbox hg,
   rc67_forcedSelfMatch_fails_witness,
   rc67_witness_marriage_holds⟩

end StatMech.Walls
