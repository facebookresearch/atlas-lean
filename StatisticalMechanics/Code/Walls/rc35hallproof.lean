/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Code.Walls.rc34butterfly

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]












noncomputable def rc35_traceSlice (𝒜 ℬ : Finset (Finset α)) (K S : Finset α) :
    Finset (Finset α) :=
  (rc10_reflInter 𝒜 ℬ).filter (fun R => R ∩ K = S ∩ K)

open Classical in







theorem rc35_slice_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K : Finset (Fin n)} (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) :
    rc35_traceSlice 𝒜 ℬ K S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc35_traceSlice, Finset.mem_filter] at hR
  obtain ⟨hRri, hRK⟩ := hR
  rw [rc20_mem_reflInter] at hRri
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨Finset.mem_univ _, hRri.1, hRri.2, K, Finset.mem_univ _,
    (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, hRK⟩



def rc35_awitsA (n : ℕ) (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun K => rc20_traceClass n K S ⊆ 𝒜)

open Classical in







theorem rc35_admOneSidedA_eq_biUnion_slice (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) :
    rc33_admOneSidedA n 𝒜 ℬ S
      = (rc35_awitsA n 𝒜 S).biUnion (fun K => rc35_traceSlice 𝒜 ℬ K S) := by
  apply Finset.Subset.antisymm
  · intro R hR
    rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq] at hR
    obtain ⟨_, hRA, hRB, K, _, hKA, hRK⟩ := hR
    rw [Finset.mem_biUnion]
    refine ⟨K, ?_, ?_⟩
    · rw [rc35_awitsA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hKA⟩
    · rw [rc35_traceSlice, Finset.mem_filter]
      exact ⟨(rc20_mem_reflInter 𝒜 ℬ R).mpr ⟨hRA, hRB⟩, hRK⟩
  · intro R hR
    rw [Finset.mem_biUnion] at hR
    obtain ⟨K, hK, hRslice⟩ := hR
    rw [rc35_awitsA, Finset.mem_filter] at hK
    exact rc35_slice_subset_admOneSidedA n 𝒜 ℬ
      ((rc20_traceClass_subset_iff n K S 𝒜).mp hK.2) hRslice









open Classical in









theorem rc35_hallOneSidedA_iff_injection (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) ↔
      ∃ f : Finset (Fin n) → Finset (Fin n),
        Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧
        ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
  set box := rc20_famCylBox 𝒜 ℬ with hbox
  constructor
  · 
    intro hHall
    set t : (↥box) → Finset (Finset (Fin n)) := fun x => rc33_admOneSidedA n 𝒜 ℬ x.val with ht
    have hHall' : ∀ s : Finset (↥box), #s ≤ #(s.biUnion t) := by
      intro s
      have hsub : s.image (Subtype.val) ⊆ box := by
        intro x hx; rw [Finset.mem_image] at hx; obtain ⟨y, _, rfl⟩ := hx; exact y.property
      have h𝒯 := hHall (s.image Subtype.val) (Finset.mem_powerset.mpr hsub)
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at h𝒯
      rwa [Finset.image_biUnion] at h𝒯
    obtain ⟨g, hinj, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall'
    
    refine ⟨fun S => if hS : S ∈ box then g ⟨S, hS⟩ else S, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      exact congrArg Subtype.val (hinj hab)
    · intro S hS
      simp only [dif_pos hS]
      exact hmem ⟨S, hS⟩
  · 
    rintro ⟨f, hinj, hmem⟩ 𝒯 h𝒯
    rw [Finset.mem_powerset] at h𝒯
    have hInjOn𝒯 : Set.InjOn f (𝒯 : Set (Finset (Fin n))) :=
      hinj.mono (by rw [Finset.coe_subset]; exact h𝒯)
    have hImgSub : 𝒯.image f ⊆ 𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ) := by
      intro R hR
      rw [Finset.mem_image] at hR
      obtain ⟨S, hS𝒯, rfl⟩ := hR
      exact Finset.mem_biUnion.mpr ⟨S, hS𝒯, hmem S (h𝒯 hS𝒯)⟩
    calc 𝒯.card = (𝒯.image f).card :=
          (Finset.card_image_of_injOn hInjOn𝒯).symm
      _ ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := Finset.card_le_card hImgSub






def rc35_OneSidedInjection : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∃ f : Finset (Fin n) → Finset (Fin n),
      Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧
      ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA n 𝒜 ℬ S

open Classical in




theorem rc35_oneSidedInjection_iff_hallOneSidedA :
    rc35_OneSidedInjection ↔ rc33_HallOneSidedA := by
  constructor
  · intro h n 𝒜 ℬ
    exact (rc35_hallOneSidedA_iff_injection n 𝒜 ℬ).mpr (h n 𝒜 ℬ)
  · intro h n 𝒜 ℬ
    exact (rc35_hallOneSidedA_iff_injection n 𝒜 ℬ).mp (h n 𝒜 ℬ)

open Classical in


theorem rc35_famCylBoxResidue_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc20_FamCylBoxResidue :=
  rc33_famCylBoxResidue_of_hallOneSidedA (rc35_oneSidedInjection_iff_hallOneSidedA.mp h)

open Classical in




theorem rc35_reimer_closes_of_oneSidedInjection (h : rc35_OneSidedInjection) :
    rc18_CylBoxReflInter :=
  rc33_reimer_closes_of_hallOneSidedA (rc35_oneSidedInjection_iff_hallOneSidedA.mp h)

open Classical in






theorem rc35_oneSidedInjection_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    ∃ f : Finset (Fin 2) → Finset (Fin 2),
      Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin 2))) ∧
      ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA 2 𝒜 ℬ S :=
  (rc35_hallOneSidedA_iff_injection 2 𝒜 ℬ).mp
    (rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ))

open Classical in






theorem rc35_oneSidedInjection_fin3_refuter :
    ∃ f : Finset (Fin 3) → Finset (Fin 3),
      Set.InjOn f (rc20_famCylBox rc32_A3 rc32_B3 : Set (Finset (Fin 3))) ∧
      ∀ S ∈ rc20_famCylBox rc32_A3 rc32_B3, f S ∈ rc33_admOneSidedA 3 rc32_A3 rc32_B3 S :=
  (rc35_hallOneSidedA_iff_injection 3 rc32_A3 rc32_B3).mp
    (rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter)














theorem rc35_box_not_subset_reflInter_fin2 :
    ¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {1}})
        ⊆ rc10_reflInter ({∅, {0}}) ({∅, {1}})) := by
  rw [← rc21_boxComp_eq, ← rc20_reflInterComp_eq]
  decide






theorem rc35_self_not_admissible_fin2 :
    (∅ : Finset (Fin 2)) ∉ rc33_admOneSidedA 2 ({∅, {0}}) ({∅, {1}}) ∅ := by
  decide









theorem rc35_minNeighbour_lt_box_fin2 :
    (rc33_admOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) {0}).card
      < (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2)))
          ({∅, {0}, {1}, {0, 1}})).card := by
  rw [← rc21_boxComp_eq]
  decide







theorem rc35_hallOneSidedA_holds_minWitness_fin2 :
    rc33_hallOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) = true := by
  decide



set_option linter.unusedVariables false in
open Classical in

































theorem rc35_reimer_hallconcrete :
    (rc35_OneSidedInjection ↔ rc33_HallOneSidedA)
      ∧ (rc35_OneSidedInjection → rc18_CylBoxReflInter)
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S K : Finset (Fin n)),
          (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) →
          rc35_traceSlice 𝒜 ℬ K S ⊆ rc33_admOneSidedA n 𝒜 ℬ S)
      ∧ (¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {1}})
          ⊆ rc10_reflInter ({∅, {0}}) ({∅, {1}})))
      ∧ ((rc33_admOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) {0}).card
          < (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2)))
              ({∅, {0}, {1}, {0, 1}})).card)
      ∧ (rc33_hallOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) = true) :=
  ⟨rc35_oneSidedInjection_iff_hallOneSidedA,
    rc35_reimer_closes_of_oneSidedInjection,
    fun n 𝒜 ℬ S K hKA => rc35_slice_subset_admOneSidedA n 𝒜 ℬ hKA,
    rc35_box_not_subset_reflInter_fin2,
    rc35_minNeighbour_lt_box_fin2,
    rc35_hallOneSidedA_holds_minWitness_fin2⟩

end StatMech.Walls
