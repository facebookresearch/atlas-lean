/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























import Code.Walls.rc18nonmono
import Code.Inequalities.ReimerButterflyStep

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









open Classical in




theorem rc19_mem_cylBoxSupp_iff_minimal (A B : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ rc18_cylBoxSupp A B ↔
      ∃ K L : Finset α, Disjoint K L ∧
        Minimal (fun T => cylinder T (supportCfg S) ⊆ A) K ∧
        Minimal (fun T => cylinder T (supportCfg S) ⊆ B) L := by
  rw [rc18_cylBoxSupp, Finset.mem_filter]
  constructor
  · rintro ⟨_, K, L, hKL, hKA, hLB⟩
    obtain ⟨K₀, hK0sub, hK0min⟩ := exists_minimal_cylinder_witness hKA
    obtain ⟨L₀, hL0sub, hL0min⟩ := exists_minimal_cylinder_witness hLB
    exact ⟨K₀, L₀,
      Finset.disjoint_of_subset_left hK0sub (Finset.disjoint_of_subset_right hL0sub hKL),
      hK0min, hL0min⟩
  · rintro ⟨K, L, hKL, hKmin, hLmin⟩
    exact ⟨Finset.mem_univ _, K, L, hKL, hKmin.1, hLmin.1⟩











open Classical in




noncomputable def rc19_cylDoubledBox (A B : Set (ConfigSpace α)) (S : Finset α) :
    Finset (Finset (α ⊕ α)) :=
  univ.filter (fun U => ∃ K L : Finset α, U = dbl K L ∧ Disjoint K L ∧
    cylinder K (supportCfg S) ⊆ A ∧ cylinder L (supportCfg S) ⊆ B)

open Classical in





theorem rc19_cylBoxSupp_iff_doubled (A B : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ rc18_cylBoxSupp A B ↔ (rc19_cylDoubledBox A B S).Nonempty := by
  rw [rc18_cylBoxSupp, Finset.mem_filter]
  constructor
  · rintro ⟨_, K, L, hKL, hKA, hLB⟩
    exact ⟨dbl K L, by
      rw [rc19_cylDoubledBox, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, K, L, rfl, hKL, hKA, hLB⟩⟩
  · rintro ⟨U, hU⟩
    rw [rc19_cylDoubledBox, Finset.mem_filter] at hU
    obtain ⟨_, K, L, _, hKL, hKA, hLB⟩ := hU
    exact ⟨Finset.mem_univ _, K, L, hKL, hKA, hLB⟩

omit [Fintype α] in




theorem rc19_dbl_inj {K L K' L' : Finset α} (h : dbl K L = dbl K' L') : K = K' ∧ L = L' := by
  have : (K, L) = (K', L') := dbl_injective (by simpa using h)
  rw [Prod.mk.injEq] at this
  exact this















theorem rc19_mem_reflInter_iff (A B : Set (ConfigSpace α)) (S : Finset α) :
    S ∈ rc10_reflInter (eventFamily A) (eventFamily B) ↔
      supportCfg S ∈ A ∧ supportCfg (Sᶜ) ∈ B := by
  classical
  rw [rc10_reflInter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨?_, ?_⟩
    · rw [rc10_mem_iff_eventFamily A, cfgSupport_supportCfg]; exact hA
    · rw [rc10_mem_iff_eventFamily B, cfgSupport_supportCfg]; exact hB
  · rintro ⟨hA, hB⟩
    refine ⟨?_, ?_⟩
    · rw [rc10_mem_iff_eventFamily A (supportCfg S), cfgSupport_supportCfg] at hA; exact hA
    · rw [rc10_mem_iff_eventFamily B (supportCfg Sᶜ), cfgSupport_supportCfg] at hB; exact hB

open Classical in





theorem rc19_reflInter_diag_injOn (A B : Set (ConfigSpace α)) :
    Set.InjOn (fun S : Finset α => dbl S Sᶜ)
      (rc10_reflInter (eventFamily A) (eventFamily B) : Set (Finset α)) := by
  intro S _ S' _ h
  simp only at h
  exact (rc19_dbl_inj h).1





















def rc19_DoubledReflection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ f : Finset α → Finset α,
    Set.InjOn f (rc18_cylBoxSupp A B : Set (Finset α)) ∧
    ∀ S ∈ rc18_cylBoxSupp A B, f S ∈ rc10_reflInter (eventFamily A) (eventFamily B)

open Classical in



theorem rc19_cylBoxReflInter_of_doubledReflection {A B : Set (ConfigSpace α)}
    (h : rc19_DoubledReflection A B) :
    #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  obtain ⟨f, hinj, hmem⟩ := h
  exact Finset.card_le_card_of_injOn f hmem hinj

open Classical in





theorem rc19_doubledReflection_of_cylBoxReflInter {A B : Set (ConfigSpace α)}
    (h : #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B))) :
    rc19_DoubledReflection A B := by
  by_cases hne : (rc18_cylBoxSupp A B).Nonempty
  · have hemb : Nonempty ((rc18_cylBoxSupp A B) ↪ (rc10_reflInter (eventFamily A) (eventFamily B))) := by
      rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter (eventFamily A) (eventFamily B))] at h
      exact Function.Embedding.nonempty_of_card_le h
    obtain ⟨e⟩ := hemb
    have htne : (rc10_reflInter (eventFamily A) (eventFamily B)).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) h
    obtain ⟨t0, ht0⟩ := htne
    refine ⟨fun S => if hS : S ∈ rc18_cylBoxSupp A B then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have : (⟨a, ha⟩ : (rc18_cylBoxSupp A B : Finset (Finset α))) = ⟨b, hb⟩ :=
        e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro S hS
      simp only [dif_pos hS]
      exact (e ⟨S, hS⟩).property
  · refine ⟨id, ?_, ?_⟩
    · intro a ha; rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne
    · intro S hS; exact absurd ⟨S, hS⟩ hne






theorem rc19_doubledReflection_iff_card (A B : Set (ConfigSpace α)) :
    rc19_DoubledReflection A B ↔
      #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) :=
  ⟨rc19_cylBoxReflInter_of_doubledReflection, rc19_doubledReflection_of_cylBoxReflInter⟩





def rc19_DoubledReflectionAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc19_DoubledReflection A B




theorem rc19_doubledReflectionAll_iff_cylBoxReflInter :
    rc19_DoubledReflectionAll ↔ rc18_CylBoxReflInter := by
  constructor
  · intro h n A B
    exact rc19_cylBoxReflInter_of_doubledReflection (h n A B)
  · intro h n A B
    exact rc19_doubledReflection_of_cylBoxReflInter (h n A B)


theorem rc19_reimerWprobCore_of_doubledReflectionAll (h : rc19_DoubledReflectionAll) :
    ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter
    (rc19_doubledReflectionAll_iff_cylBoxReflInter.mp h)

end StatMech.Walls
