/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Code.Walls.rc11core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

set_option maxRecDepth 100000

variable {α : Type*} [Fintype α] [DecidableEq α]







open Classical in

noncomputable def rc12_upGen (L0 : Finset α) : Finset (Finset α) :=
  univ.filter (L0 ⊆ ·)

open Classical in

theorem rc12_mem_upGen (L0 S : Finset α) : S ∈ rc12_upGen L0 ↔ L0 ⊆ S := by
  simp [rc12_upGen]

open Classical in

theorem rc12_upGen_isUpper (L0 : Finset α) :
    IsUpperSet ((rc12_upGen L0 : Finset (Finset α)) : Set (Finset α)) := by
  intro S T hST hS
  simp only [Finset.mem_coe, rc12_mem_upGen] at hS ⊢
  exact hS.trans (Finset.le_iff_subset.mp hST)









open Classical in





theorem rc12_reflConstraint_mem_reflInter (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    {S T R : Finset α} (hT : T ∈ 𝒜) (hST : S \ T ∈ ℬ) (hTR : T ⊆ R)
    (hdisj : Disjoint R (S \ T)) : R ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc11_mem_reflInter]
  refine ⟨h𝒜 (Finset.le_iff_subset.mpr hTR) hT, ?_⟩
  apply hℬ _ hST
  rw [Finset.le_iff_subset]
  intro a ha
  rw [Finset.mem_compl]
  exact fun haR => (Finset.disjoint_left.mp hdisj haR) ha








open Classical in







def rc12_ReimerReflectionInjection (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∃ (T R : Finset α → Finset α),
    (∀ S ∈ rc10_boxSupp 𝒜 ℬ, T S ⊆ S ∧ T S ∈ 𝒜 ∧ S \ T S ∈ ℬ ∧
      T S ⊆ R S ∧ Disjoint (R S) (S \ T S)) ∧
    Set.InjOn R (rc10_boxSupp 𝒜 ℬ)

open Classical in




theorem rc12_injection_of_reflectionInjection (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (h : rc12_ReimerReflectionInjection 𝒜 ℬ) : rc11_BKRInjection 𝒜 ℬ := by
  obtain ⟨T, R, hwit, hinj⟩ := h
  refine ⟨R, hinj, ?_⟩
  intro S hS
  obtain ⟨_, hTmem, hSTmem, hTR, hdisj⟩ := hwit S hS
  exact rc12_reflConstraint_mem_reflInter 𝒜 ℬ h𝒜 hℬ hTmem hSTmem hTR hdisj

open Classical in


theorem rc12_card_le_of_reflectionInjection (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (h : rc12_ReimerReflectionInjection 𝒜 ℬ) :
    #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc11_card_le_of_injection (rc12_injection_of_reflectionInjection 𝒜 ℬ h𝒜 hℬ h)








open Classical in


theorem rc12_boxSupp_principalRight_iff (𝒜 : Finset (Finset α)) (L0 S : Finset α) :
    S ∈ rc10_boxSupp 𝒜 (rc12_upGen L0) ↔ L0 ⊆ S ∧ ∃ T ⊆ S, T ∈ 𝒜 ∧ Disjoint T L0 := by
  rw [rc11_boxSupp_upper_split 𝒜 (rc12_upGen L0) (rc12_upGen_isUpper L0) S]
  constructor
  · rintro ⟨T, hTS, hT, hST⟩
    rw [rc12_mem_upGen] at hST
    refine ⟨hST.trans Finset.sdiff_subset, T, hTS, hT, ?_⟩
    rw [Finset.disjoint_left]
    intro a haT haL0
    have : a ∈ S \ T := hST haL0
    rw [Finset.mem_sdiff] at this
    exact this.2 haT
  · rintro ⟨hL0S, T, hTS, hT, hdisj⟩
    refine ⟨T, hTS, hT, ?_⟩
    rw [rc12_mem_upGen]
    intro a haL0
    rw [Finset.mem_sdiff]
    exact ⟨hL0S haL0, fun haT => (Finset.disjoint_right.mp hdisj haL0) haT⟩

open Classical in



theorem rc12_principalRight_image (𝒜 : Finset (Finset α)) (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (L0 : Finset α) {S : Finset α} (hS : S ∈ rc10_boxSupp 𝒜 (rc12_upGen L0)) :
    (S \ L0) ∈ rc10_reflInter 𝒜 (rc12_upGen L0) := by
  rw [rc12_boxSupp_principalRight_iff] at hS
  obtain ⟨hL0S, T, hTS, hT, hdisj⟩ := hS
  rw [rc11_mem_reflInter]
  refine ⟨?_, ?_⟩
  · apply h𝒜 _ hT
    rw [Finset.le_iff_subset]
    intro a haT
    rw [Finset.mem_sdiff]
    exact ⟨hTS haT, fun haL0 => (Finset.disjoint_left.mp hdisj haT) haL0⟩
  · rw [rc12_mem_upGen]
    intro a haL0
    rw [Finset.mem_compl, Finset.mem_sdiff]
    rintro ⟨_, hna⟩
    exact hna haL0

open Classical in



theorem rc12_principalRight_injOn (𝒜 : Finset (Finset α)) (L0 : Finset α) :
    Set.InjOn (fun S => S \ L0) (rc10_boxSupp 𝒜 (rc12_upGen L0) : Set (Finset α)) := by
  intro S hS S' hS' heq
  simp only [Finset.mem_coe] at hS hS'
  rw [rc12_boxSupp_principalRight_iff] at hS hS'
  obtain ⟨hL0S, _⟩ := hS
  obtain ⟨hL0S', _⟩ := hS'
  simp only [] at heq
  have e1 : S = (S \ L0) ∪ L0 := by rw [Finset.sdiff_union_of_subset hL0S]
  have e2 : S' = (S' \ L0) ∪ L0 := by rw [Finset.sdiff_union_of_subset hL0S']
  rw [e1, e2, heq]

open Classical in



theorem rc12_principalRight_injection (𝒜 : Finset (Finset α)) (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (L0 : Finset α) : rc11_BKRInjection 𝒜 (rc12_upGen L0) :=
  ⟨fun S => S \ L0, rc12_principalRight_injOn 𝒜 L0,
    fun _ hS => rc12_principalRight_image 𝒜 h𝒜 L0 hS⟩

open Classical in




theorem rc12_principalRight_reflectionInjection (𝒜 : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) (L0 : Finset α) :
    rc12_ReimerReflectionInjection 𝒜 (rc12_upGen L0) := by
  refine ⟨fun S => S \ L0, fun S => S \ L0, ?_, ?_⟩
  · intro S hS
    rw [rc12_boxSupp_principalRight_iff] at hS
    obtain ⟨hL0S, T, hTS, hT, hdisj⟩ := hS
    have hTSL0 : T ⊆ S \ L0 := by
      intro a haT
      rw [Finset.mem_sdiff]
      exact ⟨hTS haT, fun haL0 => (Finset.disjoint_left.mp hdisj haT) haL0⟩
    have hSL0mem : S \ L0 ∈ 𝒜 := h𝒜 (Finset.le_iff_subset.mpr hTSL0) hT
    have hSdiff : S \ (S \ L0) = L0 := by
      ext a; simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨ha, h⟩; by_contra hc; exact h ⟨ha, hc⟩
      · intro ha; exact ⟨hL0S ha, fun h => h.2 ha⟩
    refine ⟨Finset.sdiff_subset, hSL0mem, ?_, Finset.Subset.refl _, ?_⟩
    · rw [hSdiff, rc12_mem_upGen]
    · rw [hSdiff]; exact Finset.sdiff_disjoint
  · exact rc12_principalRight_injOn 𝒜 L0








open Classical in


theorem rc12_boxSupp_principalLeft_iff (ℬ : Finset (Finset α))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) (T0 S : Finset α) :
    S ∈ rc10_boxSupp (rc12_upGen T0) ℬ ↔ T0 ⊆ S ∧ S \ T0 ∈ ℬ := by
  rw [rc11_boxSupp_upper_split (rc12_upGen T0) ℬ hℬ S]
  constructor
  · rintro ⟨T, hTS, hT, hST⟩
    rw [rc12_mem_upGen] at hT
    refine ⟨hT.trans hTS, ?_⟩
    apply hℬ _ hST
    rw [Finset.le_iff_subset]
    exact Finset.sdiff_subset_sdiff (le_refl S) hT
  · rintro ⟨hT0S, hST0⟩
    exact ⟨T0, hT0S, by rw [rc12_mem_upGen], hST0⟩

open Classical in



theorem rc12_principalLeft_image (ℬ : Finset (Finset α)) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (T0 : Finset α) {S : Finset α} (hS : S ∈ rc10_boxSupp (rc12_upGen T0) ℬ) :
    (Sᶜ ∪ T0) ∈ rc10_reflInter (rc12_upGen T0) ℬ := by
  rw [rc12_boxSupp_principalLeft_iff ℬ hℬ] at hS
  obtain ⟨hT0S, hST0⟩ := hS
  rw [rc11_mem_reflInter]
  refine ⟨?_, ?_⟩
  · rw [rc12_mem_upGen]; exact Finset.subset_union_right
  · have : (Sᶜ ∪ T0)ᶜ = S \ T0 := by
      rw [Finset.compl_union, compl_compl]
      ext a; simp [Finset.mem_sdiff, and_comm]
    rw [this]; exact hST0

open Classical in



theorem rc12_principalLeft_injOn (ℬ : Finset (Finset α)) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (T0 : Finset α) :
    Set.InjOn (fun S => Sᶜ ∪ T0) (rc10_boxSupp (rc12_upGen T0) ℬ : Set (Finset α)) := by
  intro S hS S' hS' heq
  simp only [Finset.mem_coe] at hS hS'
  rw [rc12_boxSupp_principalLeft_iff ℬ hℬ] at hS hS'
  obtain ⟨hT0S, _⟩ := hS
  obtain ⟨hT0S', _⟩ := hS'
  simp only [] at heq
  have hc : (Sᶜ ∪ T0)ᶜ = (S'ᶜ ∪ T0)ᶜ := congrArg compl heq
  rw [Finset.compl_union, compl_compl, Finset.compl_union, compl_compl] at hc
  have e1 : S = (S ∩ T0ᶜ) ∪ T0 := by
    ext a; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    constructor
    · intro h; by_cases ha : a ∈ T0
      · right; exact ha
      · left; exact ⟨h, ha⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hT0S h
  have e2 : S' = (S' ∩ T0ᶜ) ∪ T0 := by
    ext a; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    constructor
    · intro h; by_cases ha : a ∈ T0
      · right; exact ha
      · left; exact ⟨h, ha⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hT0S' h
  rw [e1, e2, hc]

open Classical in



theorem rc12_principalLeft_injection (ℬ : Finset (Finset α)) (hℬ : IsUpperSet (ℬ : Set (Finset α)))
    (T0 : Finset α) : rc11_BKRInjection (rc12_upGen T0) ℬ :=
  ⟨fun S => Sᶜ ∪ T0, rc12_principalLeft_injOn ℬ hℬ T0,
    fun _ hS => rc12_principalLeft_image ℬ hℬ T0 hS⟩

open Classical in



theorem rc12_principalLeft_reflectionInjection (ℬ : Finset (Finset α))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) (T0 : Finset α) :
    rc12_ReimerReflectionInjection (rc12_upGen T0) ℬ := by
  refine ⟨fun _ => T0, fun S => Sᶜ ∪ T0, ?_, ?_⟩
  · intro S hS
    rw [rc12_boxSupp_principalLeft_iff ℬ hℬ] at hS
    obtain ⟨hT0S, hST0⟩ := hS
    refine ⟨hT0S, by rw [rc12_mem_upGen], hST0, Finset.subset_union_right, ?_⟩
    rw [Finset.disjoint_left]
    intro a haR haST0
    rw [Finset.mem_sdiff] at haST0
    rcases Finset.mem_union.mp haR with h | h
    · exact (Finset.mem_compl.mp h) haST0.1
    · exact haST0.2 h
  · exact rc12_principalLeft_injOn ℬ hℬ T0








open Classical in



theorem rc12_residue_realised_principalRight (n : ℕ) (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) (L0 : Finset (Fin n)) :
    rc12_ReimerReflectionInjection 𝒜 (rc12_upGen L0)
      ∧ rc11_BKRInjection 𝒜 (rc12_upGen L0)
      ∧ #(rc10_boxSupp 𝒜 (rc12_upGen L0)) ≤ #(rc10_reflInter 𝒜 (rc12_upGen L0)) :=
  ⟨rc12_principalRight_reflectionInjection 𝒜 h𝒜 L0,
    rc12_principalRight_injection 𝒜 h𝒜 L0,
    rc11_card_le_of_injection (rc12_principalRight_injection 𝒜 h𝒜 L0)⟩

open Classical in

theorem rc12_residue_realised_principalLeft (n : ℕ) (ℬ : Finset (Finset (Fin n)))
    (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) (T0 : Finset (Fin n)) :
    rc12_ReimerReflectionInjection (rc12_upGen T0) ℬ
      ∧ rc11_BKRInjection (rc12_upGen T0) ℬ
      ∧ #(rc10_boxSupp (rc12_upGen T0) ℬ) ≤ #(rc10_reflInter (rc12_upGen T0) ℬ) :=
  ⟨rc12_principalLeft_reflectionInjection ℬ hℬ T0,
    rc12_principalLeft_injection ℬ hℬ T0,
    rc11_card_le_of_injection (rc12_principalLeft_injection ℬ hℬ T0)⟩









def rc12_boxSuppComp (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => ∃ K ∈ 𝒜, ∃ L ∈ ℬ, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S)


def rc12_reflInterComp (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => S ∈ 𝒜 ∧ Sᶜ ∈ ℬ)

open Classical in

theorem rc12_boxSuppComp_eq (𝒜 ℬ : Finset (Finset α)) :
    rc12_boxSuppComp 𝒜 ℬ = rc10_boxSupp 𝒜 ℬ := by
  ext S
  rw [rc12_boxSuppComp, rc11_mem_boxSupp]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨K, hK, L, hL, hd, hKS, hLS⟩; exact ⟨K, L, hd, hKS, hLS, hK, hL⟩
  · rintro ⟨K, L, hd, hKS, hLS, hK, hL⟩; exact ⟨K, hK, L, hL, hd, hKS, hLS⟩

open Classical in

theorem rc12_reflInterComp_eq (𝒜 ℬ : Finset (Finset α)) :
    rc12_reflInterComp 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext S
  rw [rc12_reflInterComp, rc11_mem_reflInter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]




def rc12_isUpperFin (n : ℕ) (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ S ∈ 𝒜, ∀ T : Finset (Fin n), S ⊆ T → T ∈ 𝒜

instance (n : ℕ) (𝒜 : Finset (Finset (Fin n))) : Decidable (rc12_isUpperFin n 𝒜) := by
  unfold rc12_isUpperFin; infer_instance

open Classical in

theorem rc12_isUpperFin_iff (n : ℕ) (𝒜 : Finset (Finset (Fin n))) :
    rc12_isUpperFin n 𝒜 ↔ IsUpperSet (𝒜 : Set (Finset (Fin n))) := by
  constructor
  · intro h S T hST hS
    simp only [Finset.mem_coe] at hS ⊢
    exact h S hS T (Finset.le_iff_subset.mp hST)
  · intro h S hS T hST
    have := h (Finset.le_iff_subset.mpr hST) (by simpa using hS)
    simpa using this










def rc12_reflInjSearch (𝒜 ℬ : Finset (Finset (Fin 2))) : Bool :=
  let box := rc12_boxSuppComp 𝒜 ℬ
  decide (∃ (T R : Finset (Fin 2) → Finset (Fin 2)),
    (∀ S ∈ box, T S ⊆ S ∧ T S ∈ 𝒜 ∧ S \ T S ∈ ℬ ∧ T S ⊆ R S ∧ Disjoint (R S) (S \ T S)) ∧
    ((box.image R).card = box.card))




def rc12_naiveUnionSearch (𝒜 ℬ : Finset (Finset (Fin 2))) : Bool :=
  let box := rc12_boxSuppComp 𝒜 ℬ
  decide (∃ T : Finset (Fin 2) → Finset (Fin 2),
    (∀ S ∈ box, T S ⊆ S ∧ T S ∈ 𝒜 ∧ S \ T S ∈ ℬ) ∧
    ((box.image (fun S => T S ∪ Sᶜ)).card = box.card))

set_option maxHeartbeats 4000000 in





theorem rc12_reflInjSearch_fin2_holds :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ →
      rc12_reflInjSearch 𝒜 ℬ = true := by
  decide










set_option maxHeartbeats 2000000 in






theorem rc12_naiveUnion_refuted :
    rc12_naiveUnionSearch ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) Finset.univ = false := by
  decide

end StatMech.Walls
