/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Code.Walls.rc31doubledcover

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









open Classical in






theorem rc32_symmDiff_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    symmDiff S L ∈ rc10_reflInter 𝒜 ℬ :=
  rc21_symmDiff_mem_reflInter hKL hKA hLB









open Classical in





theorem rc32_reimer_closes_of_perSupportReflection (h : rc20_PerSupportReflection) :
    rc20_FamCylBoxResidue :=
  rc31_famCylBoxResidue_of_perSupportReflection h

open Classical in





theorem rc32_cylBoxReflInter_of_symmDiffReflection (h : rc21_SymmDiffReflection) :
    rc18_CylBoxReflInter :=
  rc31_cylBoxReflInter_of_symmDiffReflection h
















def rc32_A3 : Finset (Finset (Fin 3)) := {∅, {0}, {1}}



def rc32_B3 : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in



theorem rc32_box_card_fin3 :
    #(rc20_famCylBox rc32_A3 rc32_B3) = 2 := by
  rw [rc32_A3, rc32_B3, ← rc20_famCylBoxComp_eq]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in




theorem rc32_reflInter_card_fin3 :
    #(rc10_reflInter rc32_A3 rc32_B3) = 3 := by
  rw [rc32_A3, rc32_B3, ← rc20_reflInterComp_eq]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in






theorem rc32_wall_holds_on_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) := by
  rw [rc32_box_card_fin3, rc32_reflInter_card_fin3]; norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in











theorem rc32_localReflSearch_fin3_refuted :
    rc21_localReflSearch 3 rc32_A3 rc32_B3 = false := by
  rw [rc32_A3, rc32_B3]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in






theorem rc32_symmDiffMirror_fin3_refuted :
    ((rc21_boxComp 3 rc32_A3 rc32_B3).biUnion
        (fun S => (rc21_symmWitComp 3 rc32_A3 rc32_B3 S).image (fun L => symmDiff S L))).card
      < (rc21_boxComp 3 rc32_A3 rc32_B3).card := by
  rw [rc32_A3, rc32_B3]; decide










open Classical in







theorem rc32_generalReflection_fin3_refuter :
    ∃ f : Finset (Fin 3) → Finset (Fin 3),
      Set.InjOn f (rc20_famCylBox rc32_A3 rc32_B3 : Set (Finset (Fin 3))) ∧
      ∀ S ∈ rc20_famCylBox rc32_A3 rc32_B3, f S ∈ rc10_reflInter rc32_A3 rc32_B3 := by
  have hle := rc32_wall_holds_on_fin3_refuter
  by_cases hne : (rc20_famCylBox rc32_A3 rc32_B3).Nonempty
  · have hemb : Nonempty ((rc20_famCylBox rc32_A3 rc32_B3) ↪ (rc10_reflInter rc32_A3 rc32_B3)) := by
      rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter rc32_A3 rc32_B3)] at hle
      exact Function.Embedding.nonempty_of_card_le hle
    obtain ⟨e⟩ := hemb
    have htne : (rc10_reflInter rc32_A3 rc32_B3).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) hle
    obtain ⟨t0, ht0⟩ := htne
    refine ⟨fun S => if hS : S ∈ rc20_famCylBox rc32_A3 rc32_B3 then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have : (⟨a, ha⟩ : (rc20_famCylBox rc32_A3 rc32_B3 : Finset (Finset (Fin 3)))) = ⟨b, hb⟩ :=
        e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro S hS
      simp only [dif_pos hS]
      exact (e ⟨S, hS⟩).property
  · exact ⟨id, fun a ha => by rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne,
      fun S hS => absurd ⟨S, hS⟩ hne⟩









open Classical in







theorem rc32_symmDiffReflection_false : ¬ rc21_SymmDiffReflection := by
  intro h
  obtain ⟨K, L, hwit, hinj⟩ := h 3 rc32_A3 rc32_B3
  
  
  
  
  
  have hsub : (rc21_boxComp 3 rc32_A3 rc32_B3).image (fun S => symmDiff S (L S)) ⊆
      (rc21_boxComp 3 rc32_A3 rc32_B3).biUnion
        (fun S => (rc21_symmWitComp 3 rc32_A3 rc32_B3 S).image (fun M => symmDiff S M)) := by
    intro R hR
    rw [Finset.mem_image] at hR
    obtain ⟨S, hSbox, hSR⟩ := hR
    rw [rc21_boxComp_eq] at hSbox
    obtain ⟨hKL, hKA, hLB⟩ := hwit S hSbox
    rw [Finset.mem_biUnion]
    refine ⟨S, by rw [rc21_boxComp_eq]; exact hSbox, ?_⟩
    rw [Finset.mem_image]
    refine ⟨L S, ?_, hSR⟩
    rw [rc21_symmWitComp, Finset.mem_filter, decide_eq_true_eq]
    refine ⟨Finset.mem_univ _, K S, Finset.mem_univ _, hKL, ?_, ?_⟩
    · exact (rc20_traceClass_subset_iff 3 (K S) S rc32_A3).mpr hKA
    · exact (rc20_traceClass_subset_iff 3 (L S) S rc32_B3).mpr hLB
  
  have hcard_img : ((rc21_boxComp 3 rc32_A3 rc32_B3).image (fun S => symmDiff S (L S))).card
      = (rc21_boxComp 3 rc32_A3 rc32_B3).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    rw [rc21_boxComp_eq, Finset.mem_coe] at ha hb
    exact hinj ha hb hab
  
  have hlt := rc32_symmDiffMirror_fin3_refuted
  rw [rc32_A3, rc32_B3] at hlt
  have hle := Finset.card_le_card hsub
  rw [hcard_img] at hle
  rw [rc32_A3, rc32_B3] at hle
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)



set_option linter.unusedVariables false in
open Classical in






























theorem rc32_reimer_reflwitness :
    (∀ {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}, Disjoint K L →
        (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) →
        (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) →
        symmDiff S L ∈ rc10_reflInter 𝒜 ℬ)
      ∧ (rc20_PerSupportReflection → rc20_FamCylBoxResidue)
      ∧ (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3))
      ∧ (rc21_localReflSearch 3 rc32_A3 rc32_B3 = false)
      ∧ (¬ rc21_SymmDiffReflection) :=
  ⟨fun hKL hKA hLB => rc32_symmDiff_mem_reflInter hKL hKA hLB,
    rc32_reimer_closes_of_perSupportReflection,
    rc32_wall_holds_on_fin3_refuter,
    rc32_localReflSearch_fin3_refuted,
    rc32_symmDiffReflection_false⟩

end StatMech.Walls
