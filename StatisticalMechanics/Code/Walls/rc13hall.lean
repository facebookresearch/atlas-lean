/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.Walls.rc12reimerinjection
import Code.Walls.rc10core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]



open Classical in





noncomputable def rc13_adm (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  univ.filter (fun R => ∃ T ⊆ S, T ∈ 𝒜 ∧ S \ T ∈ ℬ ∧ T ⊆ R ∧ Disjoint R (S \ T))

open Classical in

theorem rc13_mem_adm (𝒜 ℬ : Finset (Finset α)) (S R : Finset α) :
    R ∈ rc13_adm 𝒜 ℬ S ↔ ∃ T ⊆ S, T ∈ 𝒜 ∧ S \ T ∈ ℬ ∧ T ⊆ R ∧ Disjoint R (S \ T) := by
  simp only [rc13_adm, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in



theorem rc13_adm_subset_reflInter (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (S : Finset α) : rc13_adm 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc13_mem_adm] at hR
  obtain ⟨T, _, hT, hST, hTR, hdisj⟩ := hR
  exact rc12_reflConstraint_mem_reflInter 𝒜 ℬ h𝒜 hℬ hT hST hTR hdisj








open Classical in



def rc13_MarriageCondition (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∀ 𝒯 ⊆ rc10_boxSupp 𝒜 ℬ, #𝒯 ≤ #(𝒯.biUnion (rc13_adm 𝒜 ℬ))






theorem rc13_marriage_iff_subtype (𝒜 ℬ : Finset (Finset α)) :
    rc13_MarriageCondition 𝒜 ℬ ↔
      ∀ s : Finset (rc10_boxSupp 𝒜 ℬ),
        #s ≤ #(s.biUnion (fun x => rc13_adm 𝒜 ℬ x.val)) := by
  classical
  constructor
  · intro h s
    
    have himg : (s.image (Subtype.val)).biUnion (rc13_adm 𝒜 ℬ)
        = s.biUnion (fun x => rc13_adm 𝒜 ℬ x.val) := by
      rw [Finset.image_biUnion]
    have hsub : s.image (Subtype.val) ⊆ rc10_boxSupp 𝒜 ℬ := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨x, _, rfl⟩ := ha
      exact x.property
    have hcard : #(s.image (Subtype.val)) = #s :=
      Finset.card_image_of_injective s Subtype.val_injective
    have := h (s.image (Subtype.val)) hsub
    rwa [hcard, himg] at this
  · intro h 𝒯 h𝒯
    
    set s : Finset (rc10_boxSupp 𝒜 ℬ) :=
      𝒯.subtype (fun a => a ∈ rc10_boxSupp 𝒜 ℬ) with hs
    have hmap : s.map (Function.Embedding.subtype _) = 𝒯 :=
      Finset.subtype_map_of_mem (fun a ha => h𝒯 ha)
    have hcards : #s = #𝒯 := by
      rw [← hmap, Finset.card_map]
    
    have hsval : s.image (Subtype.val) = 𝒯 := by
      rw [← hmap]
      ext a
      simp only [Finset.mem_image, Finset.mem_map, Function.Embedding.coe_subtype]
    have himg : s.biUnion (fun x => rc13_adm 𝒜 ℬ x.val) = 𝒯.biUnion (rc13_adm 𝒜 ℬ) := by
      rw [← hsval, Finset.image_biUnion]
    have := h s
    rwa [hcards, himg] at this








omit [Fintype α] in




theorem rc13_hall_abstract {ι : Type*} (t : ι → Finset (Finset α)) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ g : ι → Finset α, Function.Injective g ∧ ∀ x, g x ∈ t x :=
  Finset.all_card_le_biUnion_card_iff_exists_injective t





theorem rc13_marriage_iff_transversal (𝒜 ℬ : Finset (Finset α)) :
    rc13_MarriageCondition 𝒜 ℬ ↔
      ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α,
        Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val := by
  rw [rc13_marriage_iff_subtype]
  exact rc13_hall_abstract (fun x : rc10_boxSupp 𝒜 ℬ => rc13_adm 𝒜 ℬ x.val)









open Classical in



theorem rc13_transversal_of_reflectionInjection (𝒜 ℬ : Finset (Finset α))
    (h : rc12_ReimerReflectionInjection 𝒜 ℬ) :
    ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α,
      Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val := by
  obtain ⟨T, R, hwit, hinj⟩ := h
  refine ⟨fun x => R x.val, ?_, ?_⟩
  · intro x y hxy
    have hx : x.val ∈ (rc10_boxSupp 𝒜 ℬ : Set (Finset α)) := x.property
    have hy : y.val ∈ (rc10_boxSupp 𝒜 ℬ : Set (Finset α)) := y.property
    exact Subtype.ext (hinj hx hy hxy)
  · intro x
    obtain ⟨_, hTmem, hSTmem, hTR, hdisj⟩ := hwit x.val x.property
    rw [rc13_mem_adm]
    exact ⟨T x.val, (hwit x.val x.property).1, hTmem, hSTmem, hTR, hdisj⟩

open Classical in




theorem rc13_reflectionInjection_of_transversal (𝒜 ℬ : Finset (Finset α))
    (h : ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α,
      Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val) :
    rc12_ReimerReflectionInjection 𝒜 ℬ := by
  obtain ⟨g, hginj, hgmem⟩ := h
  
  choose Tw hTsub hTmem hSTmem hTR hdisj using fun (x : rc10_boxSupp 𝒜 ℬ) =>
    (rc13_mem_adm 𝒜 ℬ x.val (g x)).mp (hgmem x)
  
  refine ⟨fun S => if hS : S ∈ rc10_boxSupp 𝒜 ℬ then Tw ⟨S, hS⟩ else S,
          fun S => if hS : S ∈ rc10_boxSupp 𝒜 ℬ then g ⟨S, hS⟩ else S, ?_, ?_⟩
  · intro S hS
    simp only [hS, dif_pos]
    exact ⟨hTsub ⟨S, hS⟩, hTmem ⟨S, hS⟩, hSTmem ⟨S, hS⟩, hTR ⟨S, hS⟩, hdisj ⟨S, hS⟩⟩
  · intro S hSc S' hS'c heq
    simp only [Finset.mem_coe] at hSc hS'c
    simp only [hSc, hS'c, dif_pos] at heq
    have : (⟨S, hSc⟩ : rc10_boxSupp 𝒜 ℬ) = ⟨S', hS'c⟩ := hginj heq
    exact congrArg Subtype.val this







theorem rc13_marriage_iff_reflectionInjection (𝒜 ℬ : Finset (Finset α)) :
    rc13_MarriageCondition 𝒜 ℬ ↔ rc12_ReimerReflectionInjection 𝒜 ℬ := by
  rw [rc13_marriage_iff_transversal]
  exact ⟨rc13_reflectionInjection_of_transversal 𝒜 ℬ,
    rc13_transversal_of_reflectionInjection 𝒜 ℬ⟩












theorem rc13_marriage_imp_bkrInjection (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (h : rc13_MarriageCondition 𝒜 ℬ) : rc11_BKRInjection 𝒜 ℬ :=
  rc12_injection_of_reflectionInjection 𝒜 ℬ h𝒜 hℬ
    ((rc13_marriage_iff_reflectionInjection 𝒜 ℬ).mp h)


theorem rc13_marriage_imp_card_le (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (h : rc13_MarriageCondition 𝒜 ℬ) :
    #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc11_card_le_of_injection (rc13_marriage_imp_bkrInjection 𝒜 ℬ h𝒜 hℬ h)






theorem rc13_marriage_iff_card_le (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    rc13_MarriageCondition 𝒜 ℬ ↔
      (rc12_ReimerReflectionInjection 𝒜 ℬ
        ∧ #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
  rw [rc13_marriage_iff_reflectionInjection]
  constructor
  · intro h
    exact ⟨h, rc12_card_le_of_reflectionInjection 𝒜 ℬ h𝒜 hℬ h⟩
  · rintro ⟨h, _⟩; exact h








open Classical in



theorem rc13_biUnion_adm_subset_reflInter (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    (rc10_boxSupp 𝒜 ℬ).biUnion (rc13_adm 𝒜 ℬ) ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [Finset.mem_biUnion] at hR
  obtain ⟨S, _, hRS⟩ := hR
  exact rc13_adm_subset_reflInter 𝒜 ℬ h𝒜 hℬ S hRS

open Classical in




theorem rc13_marriageFull_imp_card_le (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (h : #(rc10_boxSupp 𝒜 ℬ)
        ≤ #((rc10_boxSupp 𝒜 ℬ).biUnion (rc13_adm 𝒜 ℬ))) :
    #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  h.trans (Finset.card_le_card (rc13_biUnion_adm_subset_reflInter 𝒜 ℬ h𝒜 hℬ))









def rc13_admComp (𝒜 ℬ : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  univ.filter (fun R => ∃ T ∈ 𝒜, T ⊆ S ∧ S \ T ∈ ℬ ∧ T ⊆ R ∧ Disjoint R (S \ T))

open Classical in

theorem rc13_admComp_eq (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    rc13_admComp 𝒜 ℬ S = rc13_adm 𝒜 ℬ S := by
  ext R
  rw [rc13_admComp, rc13_adm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T, hT, hTS, hST, hTR, hdisj⟩; exact ⟨T, hTS, hT, hST, hTR, hdisj⟩
  · rintro ⟨T, hTS, hT, hST, hTR, hdisj⟩; exact ⟨T, hT, hTS, hST, hTR, hdisj⟩




def rc13_marriageSearch (𝒜 ℬ : Finset (Finset (Fin 2))) : Bool :=
  decide (∀ 𝒯 ∈ (rc12_boxSuppComp 𝒜 ℬ).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc13_admComp 𝒜 ℬ)).card)

open Classical in




theorem rc13_marriageSearch_iff_marriage (𝒜 ℬ : Finset (Finset (Fin 2))) :
    rc13_marriageSearch 𝒜 ℬ = true ↔ rc13_MarriageCondition 𝒜 ℬ := by
  have hfun : rc13_admComp 𝒜 ℬ = rc13_adm 𝒜 ℬ := funext (rc13_admComp_eq 𝒜 ℬ)
  rw [rc13_marriageSearch, decide_eq_true_eq, rc13_MarriageCondition]
  constructor
  · intro h 𝒯 h𝒯
    have h𝒯' : 𝒯 ∈ (rc12_boxSuppComp 𝒜 ℬ).powerset := by
      rw [Finset.mem_powerset, rc12_boxSuppComp_eq]; exact h𝒯
    have := h 𝒯 h𝒯'
    rwa [hfun] at this
  · intro h 𝒯 h𝒯
    rw [Finset.mem_powerset, rc12_boxSuppComp_eq] at h𝒯
    have := h 𝒯 h𝒯
    rwa [hfun]





set_option maxHeartbeats 8000000 in









theorem rc13_marriageSearch_iff_card_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
      (rc13_marriageSearch 𝒜 ℬ = true ↔
        (rc12_boxSuppComp 𝒜 ℬ).card ≤ (rc12_reflInterComp 𝒜 ℬ).card) := by
  decide

set_option maxHeartbeats 4000000 in





theorem rc13_marriageSearch_fin2_holds :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
      rc13_marriageSearch 𝒜 ℬ = true := by
  decide

























theorem rc13_hall_route_is_circular :
    (∀ 𝒜 ℬ : Finset (Finset α),
        rc13_MarriageCondition 𝒜 ℬ ↔ rc12_ReimerReflectionInjection 𝒜 ℬ)
      ∧ (∀ 𝒜 ℬ : Finset (Finset α),
          rc13_MarriageCondition 𝒜 ℬ ↔
            ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α,
              Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val)
      ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
          (rc13_marriageSearch 𝒜 ℬ = true ↔
            (rc12_boxSuppComp 𝒜 ℬ).card ≤ (rc12_reflInterComp 𝒜 ℬ).card)) :=
  ⟨rc13_marriage_iff_reflectionInjection,
    rc13_marriage_iff_transversal,
    rc13_marriageSearch_iff_card_fin2⟩

end StatMech.Walls
