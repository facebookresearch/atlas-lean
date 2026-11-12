/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Code.Walls.rc32reflwitness
import Mathlib.Combinatorics.Hall.Basic

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]

















def rc33_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧
    ∃ K ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) = true)



def rc33_admOneSidedB (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧
    ∃ L ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n L S ⊆ ℬ ∧ Rᶜ ∩ L = S ∩ L) = true)






def rc33_admBothSided (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧
    (∃ K ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) ∧
    (∃ L ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n L S ⊆ ℬ ∧ Rᶜ ∩ L = S ∩ L)) = true)










theorem rc33_admOneSidedA_subset_reflInter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc33_admOneSidedA n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, hRA, hRB, _⟩ := hR
  rw [rc20_mem_reflInter]; exact ⟨hRA, hRB⟩


theorem rc33_admOneSidedB_subset_reflInter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc33_admOneSidedB n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc33_admOneSidedB, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, hRA, hRB, _⟩ := hR
  rw [rc20_mem_reflInter]; exact ⟨hRA, hRB⟩






theorem rc33_admComp_subset_bothSided (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc21_admComp n 𝒜 ℬ S ⊆ rc33_admBothSided n 𝒜 ℬ S := by
  intro R hR
  rw [rc21_admComp, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, K, _, L, _, hKL, hKA, hLB, hRK, hRL⟩ := hR
  rw [rc33_admBothSided, Finset.mem_filter, decide_eq_true_eq]
  have hmem : R ∈ rc10_reflInter 𝒜 ℬ :=
    rc21_localRefl_mem_reflInter ((rc20_traceClass_subset_iff n K S 𝒜).mp hKA)
      ((rc20_traceClass_subset_iff n L S ℬ).mp hLB) hRK hRL
  rw [rc20_mem_reflInter] at hmem
  exact ⟨Finset.mem_univ _, hmem.1, hmem.2,
    ⟨K, Finset.mem_univ _, hKA, hRK⟩, ⟨L, Finset.mem_univ _, hLB, hRL⟩⟩










open Classical in









theorem rc33_wall_of_hallOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  set box := rc20_famCylBox 𝒜 ℬ with hbox
  set t : (↥box) → Finset (Finset (Fin n)) := fun x => rc33_admOneSidedA n 𝒜 ℬ x.val with ht
  
  have hHall' : ∀ s : Finset (↥box), #s ≤ #(s.biUnion t) := by
    intro s
    have hsub : s.image (Subtype.val) ⊆ box := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨y, _, rfl⟩ := hx; exact y.property
    have h𝒯 := hHall (s.image Subtype.val) (Finset.mem_powerset.mpr hsub)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h𝒯
    rwa [Finset.image_biUnion] at h𝒯
  
  obtain ⟨g, hinj, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall'
  have hg_ri : ∀ x, g x ∈ rc10_reflInter 𝒜 ℬ := fun x =>
    rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ x.val (hmem x)
  
  have hcard : Fintype.card (↥box) ≤ Fintype.card (↥(rc10_reflInter 𝒜 ℬ)) := by
    refine Fintype.card_le_of_injective (fun x => (⟨g x, hg_ri x⟩ : ↥(rc10_reflInter 𝒜 ℬ))) ?_
    intro a b hab
    exact hinj (Subtype.ext_iff.mp hab)
  rwa [Fintype.card_coe, Fintype.card_coe] at hcard









open Classical in




theorem rc33_hallComplete_iff_wall (𝒜 ℬ : Finset (Finset α)) :
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (fun _ => rc10_reflInter 𝒜 ℬ)).card) ↔
      #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  constructor
  · intro h
    have hbox := h (rc20_famCylBox 𝒜 ℬ) (Finset.mem_powerset.mpr (Finset.Subset.refl _))
    rcases (rc20_famCylBox 𝒜 ℬ).eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · rwa [show (rc20_famCylBox 𝒜 ℬ).biUnion (fun _ => rc10_reflInter 𝒜 ℬ)
          = rc10_reflInter 𝒜 ℬ from ?_] at hbox
      apply Finset.Subset.antisymm
      · exact Finset.biUnion_subset.mpr (fun _ _ => Finset.Subset.refl _)
      · obtain ⟨i, hi⟩ := hne
        exact fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  · intro hcard 𝒯 h𝒯
    rw [Finset.mem_powerset] at h𝒯
    rcases 𝒯.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · rw [show 𝒯.biUnion (fun _ => rc10_reflInter 𝒜 ℬ) = rc10_reflInter 𝒜 ℬ from ?_]
      · exact le_trans (Finset.card_le_card h𝒯) hcard
      · apply Finset.Subset.antisymm
        · exact Finset.biUnion_subset.mpr (fun _ _ => Finset.Subset.refl _)
        · obtain ⟨i, hi⟩ := hne
          exact fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩













def rc33_HallOneSidedA : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card

open Classical in


theorem rc33_famCylBoxResidue_of_hallOneSidedA (h : rc33_HallOneSidedA) :
    rc20_FamCylBoxResidue :=
  fun n 𝒜 ℬ => rc33_wall_of_hallOneSidedA n 𝒜 ℬ (h n 𝒜 ℬ)

open Classical in




theorem rc33_perSupportReflection_of_hallOneSidedA (h : rc33_HallOneSidedA) :
    rc20_PerSupportReflection :=
  rc20_perSupportReflection_iff_famCylBoxResidue.mpr (rc33_famCylBoxResidue_of_hallOneSidedA h)

open Classical in




theorem rc33_reimer_closes_of_hallOneSidedA (h : rc33_HallOneSidedA) :
    rc18_CylBoxReflInter :=
  rc20_perSupportReflection_iff_cylBoxReflInter.mp (rc33_perSupportReflection_of_hallOneSidedA h)









def rc33_hallOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ 𝒯 ∈ (rc21_boxComp n 𝒜 ℬ).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card)


def rc33_hallBothSided (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ 𝒯 ∈ (rc21_boxComp n 𝒜 ℬ).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc33_admBothSided n 𝒜 ℬ)).card)

open Classical in


theorem rc33_hallOneSidedA_prop_of_bool (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc33_hallOneSidedA n 𝒜 ℬ = true) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  rw [rc33_hallOneSidedA, decide_eq_true_eq, rc21_boxComp_eq] at h
  exact h









theorem rc33_hallOneSidedA_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    rc33_hallOneSidedA 0 𝒜 ℬ = true := by revert 𝒜 ℬ; decide


theorem rc33_hallOneSidedA_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    rc33_hallOneSidedA 1 𝒜 ℬ = true := by revert 𝒜 ℬ; decide

set_option maxHeartbeats 4000000 in




theorem rc33_hallOneSidedA_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    rc33_hallOneSidedA 2 𝒜 ℬ = true := by revert 𝒜 ℬ; decide

open Classical in





theorem rc33_wall_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc33_wall_of_hallOneSidedA 2 𝒜 ℬ (rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ))










set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in





theorem rc33_hallOneSidedA_fin3_refuter :
    rc33_hallOneSidedA 3 rc32_A3 rc32_B3 = true := by
  rw [rc32_A3, rc32_B3]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in







theorem rc33_hallBothSided_fin3_refuted :
    rc33_hallBothSided 3 rc32_A3 rc32_B3 = false := by
  rw [rc32_A3, rc32_B3]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in






theorem rc33_admOneSidedA_proper_fin3 :
    rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3 := by
  rw [rc32_A3, rc32_B3, ← rc20_reflInterComp_eq]; decide






theorem rc33_wall_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) :=
  rc33_wall_of_hallOneSidedA 3 rc32_A3 rc32_B3
    (rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter)



set_option linter.unusedVariables false in
open Classical in

































theorem rc33_reimer_nonlocal :
    (rc33_HallOneSidedA → rc20_PerSupportReflection)
      ∧ (rc33_HallOneSidedA → rc18_CylBoxReflInter)
      ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc33_hallOneSidedA 3 rc32_A3 rc32_B3 = true)
      ∧ (rc33_hallBothSided 3 rc32_A3 rc32_B3 = false)
      ∧ (rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3) :=
  ⟨rc33_perSupportReflection_of_hallOneSidedA,
    rc33_reimer_closes_of_hallOneSidedA,
    rc33_wall_fin2,
    rc33_hallOneSidedA_fin3_refuter,
    rc33_hallBothSided_fin3_refuted,
    rc33_admOneSidedA_proper_fin3⟩

end StatMech.Walls
