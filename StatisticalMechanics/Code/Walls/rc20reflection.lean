/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.Walls.rc19doublecover

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







open Classical in



theorem rc20_mem_eventFamily_iff (A : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ eventFamily A ↔ supportCfg S ∈ A := by
  rw [rc10_mem_iff_eventFamily A (supportCfg S), cfgSupport_supportCfg]

open Classical in


theorem rc20_eventFamily_univ : eventFamily (Set.univ : Set (ConfigSpace α)) = univ := by
  ext S
  simp only [rc20_mem_eventFamily_iff, Set.mem_univ, Finset.mem_univ]











omit [Fintype α] in


theorem rc20_agree_iff_inter (K S T : Finset α) :
    (∀ e ∈ K, supportCfg T e = supportCfg S e) ↔ T ∩ K = S ∩ K := by
  constructor
  · intro h
    ext e
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨heT, heK⟩
      have := h e heK
      simp only [supportCfg_apply, decide_eq_decide] at this
      exact ⟨this.mp heT, heK⟩
    · rintro ⟨heS, heK⟩
      have := h e heK
      simp only [supportCfg_apply, decide_eq_decide] at this
      exact ⟨this.mpr heS, heK⟩
  · intro h e heK
    simp only [supportCfg_apply, decide_eq_decide]
    constructor
    · intro heT
      have : e ∈ T ∩ K := Finset.mem_inter.mpr ⟨heT, heK⟩
      rw [h] at this
      exact (Finset.mem_inter.mp this).1
    · intro heS
      have : e ∈ S ∩ K := Finset.mem_inter.mpr ⟨heS, heK⟩
      rw [← h] at this
      exact (Finset.mem_inter.mp this).1

open Classical in






theorem rc20_cylinder_subset_iff_family (A : Set (ConfigSpace α)) (K S : Finset α) :
    cylinder K (supportCfg S) ⊆ A ↔ ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ eventFamily A := by
  constructor
  · intro hcyl T hT
    rw [rc20_mem_eventFamily_iff]
    apply hcyl
    rw [mem_cylinder]
    exact (rc20_agree_iff_inter K S T).mpr hT
  · intro hfam ω' hω'
    rw [mem_cylinder] at hω'
    
    have hkey : cfgSupport ω' ∈ eventFamily A := by
      apply hfam
      apply (rc20_agree_iff_inter K S (cfgSupport ω')).mp
      intro e heK
      rw [supportCfg_cfgSupport]
      exact hω' e heK
    rw [rc20_mem_eventFamily_iff, supportCfg_cfgSupport] at hkey
    exact hkey










open Classical in



theorem rc20_cylBoxSupp_self_mem {A B : Set (ConfigSpace α)} {S : Finset α}
    (hS : S ∈ rc18_cylBoxSupp A B) : supportCfg S ∈ A ∧ supportCfg S ∈ B := by
  rw [rc18_cylBoxSupp, Finset.mem_filter] at hS
  obtain ⟨_, K, L, _, hKA, hLB⟩ := hS
  exact ⟨hKA (self_mem_cylinder K (supportCfg S)), hLB (self_mem_cylinder L (supportCfg S))⟩

open Classical in


theorem rc20_cylBoxSupp_mem_eventFamily {A B : Set (ConfigSpace α)} {S : Finset α}
    (hS : S ∈ rc18_cylBoxSupp A B) : S ∈ eventFamily A :=
  (rc20_mem_eventFamily_iff A S).mpr (rc20_cylBoxSupp_self_mem hS).1










open Classical in



noncomputable def rc20_famCylBox (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => ∃ K L : Finset α, Disjoint K L ∧
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ))

open Classical in




theorem rc20_cylBoxSupp_eq_famCylBox (A B : Set (ConfigSpace α)) :
    rc18_cylBoxSupp A B = rc20_famCylBox (eventFamily A) (eventFamily B) := by
  ext S
  rw [rc18_cylBoxSupp, rc20_famCylBox, Finset.mem_filter, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc20_cylinder_subset_iff_family A K S).mp hKA,
      (rc20_cylinder_subset_iff_family B L S).mp hLB⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc20_cylinder_subset_iff_family A K S).mpr hKA,
      (rc20_cylinder_subset_iff_family B L S).mpr hLB⟩

open Classical in


theorem rc20_mem_reflInter (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc10_reflInter 𝒜 ℬ ↔ S ∈ 𝒜 ∧ Sᶜ ∈ ℬ := by
  rw [rc10_reflInter, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩














def rc20_FamCylBoxResidue : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)

open Classical in


theorem rc20_cylBoxReflInter_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) : rc18_CylBoxReflInter := by
  intro n A B
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact h n (eventFamily A) (eventFamily B)

open Classical in




theorem rc20_famCylBoxResidue_of_cylBoxReflInter (h : rc18_CylBoxReflInter) : rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  have hkey := h n (familyEvent 𝒜) (familyEvent ℬ)
  rw [rc20_cylBoxSupp_eq_famCylBox, rc10_eventFamily_familyEvent, rc10_eventFamily_familyEvent]
    at hkey
  exact hkey





theorem rc20_famCylBoxResidue_iff_cylBoxReflInter :
    rc20_FamCylBoxResidue ↔ rc18_CylBoxReflInter :=
  ⟨rc20_cylBoxReflInter_of_famCylBoxResidue, rc20_famCylBoxResidue_of_cylBoxReflInter⟩








open Classical in




theorem rc20_doubledReflection_right_univ (A : Set (ConfigSpace α)) :
    rc19_DoubledReflection A (Set.univ : Set (ConfigSpace α)) := by
  refine ⟨id, Set.injOn_id _, ?_⟩
  intro S hS
  rw [rc19_mem_reflInter_iff]
  refine ⟨?_, ?_⟩
  · exact (rc20_cylBoxSupp_self_mem hS).1
  · exact Set.mem_univ _

open Classical in





theorem rc20_doubledReflection_left_univ (B : Set (ConfigSpace α)) :
    rc19_DoubledReflection (Set.univ : Set (ConfigSpace α)) B := by
  refine ⟨fun S : Finset α => Sᶜ, ?_, ?_⟩
  · intro S _ S' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this
  · intro S hS
    rw [rc19_mem_reflInter_iff]
    refine ⟨Set.mem_univ _, ?_⟩
    rw [compl_compl]
    exact (rc20_cylBoxSupp_self_mem hS).2









def rc20_traceClass (n : ℕ) (K S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  univ.filter (fun T => T ∩ K = S ∩ K)



def rc20_famCylBoxComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => decide (∃ K ∈ (univ : Finset (Finset (Fin n))),
    ∃ L ∈ (univ : Finset (Finset (Fin n))), Disjoint K L ∧
      rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ) = true)


def rc20_reflInterComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => decide (S ∈ 𝒜 ∧ Sᶜ ∈ ℬ) = true)



theorem rc20_traceClass_subset_iff (n : ℕ) (K S : Finset (Fin n)) (𝒜 : Finset (Finset (Fin n))) :
    rc20_traceClass n K S ⊆ 𝒜 ↔ ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜 := by
  rw [rc20_traceClass]
  constructor
  · intro h T hT
    exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)
  · intro h T hT
    rw [Finset.mem_filter] at hT
    exact h T hT.2

open Classical in

theorem rc20_famCylBoxComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc20_famCylBoxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
  ext S
  rw [rc20_famCylBoxComp, rc20_famCylBox, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, _, L, _, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc20_traceClass_subset_iff n K S 𝒜).mp hKA,
      (rc20_traceClass_subset_iff n L S ℬ).mp hLB⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨K, Finset.mem_univ _, L, Finset.mem_univ _, hKL,
      (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, (rc20_traceClass_subset_iff n L S ℬ).mpr hLB⟩

open Classical in

theorem rc20_reflInterComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc20_reflInterComp n 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext S
  rw [rc20_reflInterComp, rc10_reflInter, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]




theorem rc20_famCylBox_card_le_iff_comp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
      (rc20_famCylBoxComp n 𝒜 ℬ).card ≤ (rc20_reflInterComp n 𝒜 ℬ).card := by
  rw [rc20_famCylBoxComp_eq, rc20_reflInterComp_eq]










theorem rc20_famCylBox_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc20_famCylBox_card_le_iff_comp]
  revert 𝒜 ℬ
  decide



theorem rc20_famCylBox_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc20_famCylBox_card_le_iff_comp]
  revert 𝒜 ℬ
  decide

set_option maxHeartbeats 4000000 in






theorem rc20_famCylBox_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc20_famCylBox_card_le_iff_comp]
  revert 𝒜 ℬ
  decide










open Classical in




theorem rc20_cylBoxReflInter_fin2 (A B : Set (ConfigSpace (Fin 2))) :
    #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc20_famCylBox_fin2 (eventFamily A) (eventFamily B)

open Classical in







theorem rc20_doubledReflection_fin2 (A B : Set (ConfigSpace (Fin 2))) :
    rc19_DoubledReflection A B :=
  rc19_doubledReflection_of_cylBoxReflInter (rc20_cylBoxReflInter_fin2 A B)

open Classical in

theorem rc20_doubledReflection_fin1 (A B : Set (ConfigSpace (Fin 1))) :
    rc19_DoubledReflection A B := by
  apply rc19_doubledReflection_of_cylBoxReflInter
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc20_famCylBox_fin1 (eventFamily A) (eventFamily B)

open Classical in

theorem rc20_doubledReflection_fin0 (A B : Set (ConfigSpace (Fin 0))) :
    rc19_DoubledReflection A B := by
  apply rc19_doubledReflection_of_cylBoxReflInter
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc20_famCylBox_fin0 (eventFamily A) (eventFamily B)










open Classical in








theorem rc20_identityMirror_insufficient :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (S : Finset (Fin 2)),
      S ∈ rc20_famCylBox 𝒜 ℬ ∧ S ∉ rc10_reflInter 𝒜 ℬ := by
  refine ⟨{∅, {0}, {1}}, {∅, {1}, {0, 1}}, {1}, ?_, ?_⟩
  · rw [← rc20_famCylBoxComp_eq]; decide
  · rw [← rc20_reflInterComp_eq]; decide








open Classical in



theorem rc20_famCylBox_mono_left {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    rc20_famCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜' ℬ := by
  intro S hS
  rw [rc20_famCylBox, Finset.mem_filter] at hS ⊢
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  exact ⟨Finset.mem_univ _, K, L, hKL, fun T hT => h (hKA T hT), hLB⟩

open Classical in


theorem rc20_famCylBox_mono_right {𝒜 ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    rc20_famCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜 ℬ' := by
  intro S hS
  rw [rc20_famCylBox, Finset.mem_filter] at hS ⊢
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  exact ⟨Finset.mem_univ _, K, L, hKL, hKA, fun T hT => h (hLB T hT)⟩









open Classical in





theorem rc20_famCylBox_of_increasing {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    #(rc20_famCylBox (eventFamily A) (eventFamily B))
      ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  rw [← rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc18_cylBoxReflInter_of_bkr hA hB







open Classical in




theorem rc20_doubledReflection_rbi :
    ((¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B))
      ∧ rc19_DoubledReflection rbi_A rbi_B :=
  ⟨⟨rc17_rbiB_not_increasing, rc17_rbiB_not_decreasing⟩, rc20_doubledReflection_fin2 rbi_A rbi_B⟩












open Classical in



def rc20_PerSupportReflection : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∃ f : Finset (Fin n) → Finset (Fin n),
      Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧
      ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc10_reflInter 𝒜 ℬ

open Classical in




theorem rc20_perSupportReflection_iff_famCylBoxResidue :
    rc20_PerSupportReflection ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    obtain ⟨f, hinj, hmem⟩ := h n 𝒜 ℬ
    exact Finset.card_le_card_of_injOn f hmem hinj
  · intro h n 𝒜 ℬ
    by_cases hne : (rc20_famCylBox 𝒜 ℬ).Nonempty
    · have hle := h n 𝒜 ℬ
      have hemb : Nonempty ((rc20_famCylBox 𝒜 ℬ) ↪ (rc10_reflInter 𝒜 ℬ)) := by
        rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter 𝒜 ℬ)] at hle
        exact Function.Embedding.nonempty_of_card_le hle
      obtain ⟨e⟩ := hemb
      have htne : (rc10_reflInter 𝒜 ℬ).Nonempty := by
        rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) (h n 𝒜 ℬ)
      obtain ⟨t0, ht0⟩ := htne
      refine ⟨fun S => if hS : S ∈ rc20_famCylBox 𝒜 ℬ then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
      · intro a ha b hb hab
        rw [Finset.mem_coe] at ha hb
        simp only [dif_pos ha, dif_pos hb] at hab
        have : (⟨a, ha⟩ : (rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin n)))) = ⟨b, hb⟩ :=
          e.injective (Subtype.ext hab)
        exact congrArg Subtype.val this
      · intro S hS
        simp only [dif_pos hS]
        exact (e ⟨S, hS⟩).property
    · exact ⟨id, fun a ha => by rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne,
        fun S hS => absurd ⟨S, hS⟩ hne⟩



theorem rc20_perSupportReflection_iff_cylBoxReflInter :
    rc20_PerSupportReflection ↔ rc18_CylBoxReflInter :=
  rc20_perSupportReflection_iff_famCylBoxResidue.trans rc20_famCylBoxResidue_iff_cylBoxReflInter

open Classical in







theorem rc20_perSupportReflection_satisfiable_rbi :
    ∃ f : Finset (Fin 2) → Finset (Fin 2),
      Set.InjOn f (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}})
        : Set (Finset (Fin 2))) ∧
      ∀ S ∈ rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}}),
        f S ∈ rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}}) := by
  set 𝒜 : Finset (Finset (Fin 2)) := {∅, {0}, {1}} with h𝒜
  set ℬ : Finset (Finset (Fin 2)) := {∅, {1}, {0, 1}} with hℬ
  have hle := rc20_famCylBox_fin2 𝒜 ℬ
  by_cases hne : (rc20_famCylBox 𝒜 ℬ).Nonempty
  · have hemb : Nonempty ((rc20_famCylBox 𝒜 ℬ) ↪ (rc10_reflInter 𝒜 ℬ)) := by
      rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter 𝒜 ℬ)] at hle
      exact Function.Embedding.nonempty_of_card_le hle
    obtain ⟨e⟩ := hemb
    have htne : (rc10_reflInter 𝒜 ℬ).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) hle
    obtain ⟨t0, ht0⟩ := htne
    refine ⟨fun S => if hS : S ∈ rc20_famCylBox 𝒜 ℬ then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have : (⟨a, ha⟩ : (rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin 2)))) = ⟨b, hb⟩ :=
        e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro S hS
      simp only [dif_pos hS]
      exact (e ⟨S, hS⟩).property
  · exact ⟨id, fun a ha => by rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne,
      fun S hS => absurd ⟨S, hS⟩ hne⟩



open Classical in




























theorem rc20_reimer_reflection :
    (rc20_FamCylBoxResidue ↔ rc18_CylBoxReflInter)
      ∧ (rc20_PerSupportReflection ↔ rc18_CylBoxReflInter)
      ∧ (∀ A B : Set (ConfigSpace (Fin 2)), rc19_DoubledReflection A B)
      ∧ (∀ A : Set (ConfigSpace α), rc19_DoubledReflection A (Set.univ : Set (ConfigSpace α)))
      ∧ (∀ B : Set (ConfigSpace α), rc19_DoubledReflection (Set.univ : Set (ConfigSpace α)) B)
      ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (S : Finset (Fin 2)),
          S ∈ rc20_famCylBox 𝒜 ℬ ∧ S ∉ rc10_reflInter 𝒜 ℬ) :=
  ⟨rc20_famCylBoxResidue_iff_cylBoxReflInter,
    rc20_perSupportReflection_iff_cylBoxReflInter,
    rc20_doubledReflection_fin2,
    rc20_doubledReflection_right_univ,
    rc20_doubledReflection_left_univ,
    rc20_identityMirror_insufficient⟩

end StatMech.Walls
