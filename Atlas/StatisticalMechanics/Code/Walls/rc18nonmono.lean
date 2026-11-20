/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Code.Walls.rc17arbitrary
import Code.Walls.rc10core
import Code.Walls.rmr_cylinderwitness

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









open Classical in





noncomputable def rc18_cylBoxSupp (A B : Set (ConfigSpace α)) : Finset (Finset α) :=
  univ.filter (fun S => ∃ K L : Finset α, Disjoint K L ∧
    cylinder K (supportCfg S) ⊆ A ∧ cylinder L (supportCfg S) ⊆ B)

open Classical in







theorem rc18_card_box_eq_cylBoxSupp (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))
      = #(rc18_cylBoxSupp A B) := by
  classical
  apply Finset.card_bij (fun ω _ => cfgSupport ω)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [mem_disjointOccurrence_iff_cylinder] at hω
    obtain ⟨K, L, hKL, hKA, hLB⟩ := hω
    rw [rc18_cylBoxSupp, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, K, L, hKL, ?_, ?_⟩
    · rwa [supportCfg_cfgSupport]
    · rwa [supportCfg_cfgSupport]
  · intro a _ b _ hab
    have := congrArg supportCfg hab
    rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
  · intro S hS
    rw [rc18_cylBoxSupp, Finset.mem_filter] at hS
    obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
    refine ⟨supportCfg S, ?_, cfgSupport_supportCfg S⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_disjointOccurrence_iff_cylinder]
    exact ⟨K, L, hKL, hKA, hLB⟩
















def rc18_CylBoxReflInter : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
    #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B))

open Classical in




theorem rc18_deficit_of_cylBoxReflInter (h : rc18_CylBoxReflInter) {n : ℕ}
    (A B : Set (ConfigSpace (Fin n))) : rc5_deficit A B ≤ 0 := by
  rw [rc5_deficit, rc18_card_box_eq_cylBoxSupp A B, rc10_card_reflInter_eq A B]
  have hle := h n A B
  have : (#(rc18_cylBoxSupp A B) : ℤ) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
    exact_mod_cast hle
  omega




theorem rc18_nonMonotone_of_cylBoxReflInter (h : rc18_CylBoxReflInter) : rc17_NonMonotoneDeficit :=
  fun _ A B _ => rc18_deficit_of_cylBoxReflInter h A B

open Classical in



theorem rc18_cylBoxReflInter_of_deficitBridge (h : rc7_DeficitBridge) : rc18_CylBoxReflInter := by
  intro n A B
  have hd := h n A B
  rw [rc5_deficit, rc18_card_box_eq_cylBoxSupp A B, rc10_card_reflInter_eq A B] at hd
  have : (#(rc18_cylBoxSupp A B) : ℤ) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
    omega
  exact_mod_cast this





theorem rc18_deficitBridge_iff_cylBoxReflInter : rc7_DeficitBridge ↔ rc18_CylBoxReflInter :=
  ⟨rc18_cylBoxReflInter_of_deficitBridge,
    fun h => rc17_deficitBridge_of_nonMonotone (rc18_nonMonotone_of_cylBoxReflInter h)⟩





theorem rc18_cylBoxReflInter_iff_nonMonotone :
    rc18_CylBoxReflInter ↔ rc17_NonMonotoneDeficit := by
  rw [← rc18_deficitBridge_iff_cylBoxReflInter, rc17_deficitBridge_iff_nonMonotone]








theorem rc18_reimerWprobCore_of_cylBoxReflInter (h : rc18_CylBoxReflInter) : ReimerWprobCore :=
  rc17_reimerWprobCore_of_nonMonotone (rc18_nonMonotone_of_cylBoxReflInter h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in



theorem rc18_reimer_inequality_of_cylBoxReflInter (h : rc18_CylBoxReflInter) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc17_reimer_inequality_of_nonMonotone (rc18_nonMonotone_of_cylBoxReflInter h) hp A B










open Classical in






theorem rc18_cylBoxSupp_subset_boxSupp (A B : Set (ConfigSpace α)) :
    rc18_cylBoxSupp A B ⊆ rc10_boxSupp (eventFamily A) (eventFamily B) := by
  intro S hS
  rw [rc18_cylBoxSupp, Finset.mem_filter] at hS
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  rw [rc10_boxSupp, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S ∩ K, S ∩ L, ?_, Finset.inter_subset_left,
    Finset.inter_subset_left, ?_, ?_⟩
  · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hKL)
  · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨supportCfg (S ∩ K), ?_, cfgSupport_supportCfg _⟩
    apply hKA
    rw [mem_cylinder]
    intro e he
    simp only [supportCfg_apply, Finset.mem_inter]
    by_cases hs : e ∈ S <;> simp [hs, he]
  · simp only [eventFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨supportCfg (S ∩ L), ?_, cfgSupport_supportCfg _⟩
    apply hLB
    rw [mem_cylinder]
    intro e he
    simp only [supportCfg_apply, Finset.mem_inter]
    by_cases hs : e ∈ S <;> simp [hs, he]


theorem rc18_card_cylBoxSupp_le_boxSupp (A B : Set (ConfigSpace α)) :
    #(rc18_cylBoxSupp A B) ≤ #(rc10_boxSupp (eventFamily A) (eventFamily B)) :=
  Finset.card_le_card (rc18_cylBoxSupp_subset_boxSupp A B)

open Classical in





theorem rc18_card_box_le_boxSupp (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))
      ≤ #(rc10_boxSupp (eventFamily A) (eventFamily B)) := by
  rw [rc18_card_box_eq_cylBoxSupp A B]
  exact rc18_card_cylBoxSupp_le_boxSupp A B











open Classical in








theorem rc18_familyBKR_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
        #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
  intro h
  have hbad := h 1 {∅} {∅}
  revert hbad
  decide









open Classical in







theorem rc18_cylBoxReflInter_of_bkr {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  have hdef : rc5_deficit A B ≤ 0 := rc10_deficit_incInc_of_bkr rc16_bkrSetFamily hA hB
  rw [rc5_deficit, rc18_card_box_eq_cylBoxSupp A B, rc10_card_reflInter_eq A B] at hdef
  have : (#(rc18_cylBoxSupp A B) : ℤ) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
    omega
  exact_mod_cast this














theorem rc18_cylBoxReflInter_rbi :
    ((¬ IsIncreasing rbi_A ∧ ¬ IsDecreasing rbi_A)
        ∨ (¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B))
      ∧ #(rc18_cylBoxSupp rbi_A rbi_B)
          ≤ #(rc10_reflInter (eventFamily rbi_A) (eventFamily rbi_B)) := by
  refine ⟨Or.inr ⟨rc17_rbiB_not_increasing, rc17_rbiB_not_decreasing⟩, ?_⟩
  have hdef : rc5_deficit rbi_A rbi_B ≤ 0 := rc7_deficit_rbi
  rw [rc5_deficit, rc18_card_box_eq_cylBoxSupp rbi_A rbi_B,
    rc10_card_reflInter_eq rbi_A rbi_B] at hdef
  have : (#(rc18_cylBoxSupp rbi_A rbi_B) : ℤ)
      ≤ #(rc10_reflInter (eventFamily rbi_A) (eventFamily rbi_B)) := by omega
  exact_mod_cast this



open Classical in


















theorem rc18_nonmono_reimer :
    (rc18_CylBoxReflInter ↔ rc17_NonMonotoneDeficit)
      ∧ (rc18_CylBoxReflInter → ReimerWprobCore)
      ∧ (∀ (A B : Set (ConfigSpace α)),
          #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))
            ≤ #(rc10_boxSupp (eventFamily A) (eventFamily B)))
      ∧ ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
            #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :=
  ⟨rc18_cylBoxReflInter_iff_nonMonotone,
    rc18_reimerWprobCore_of_cylBoxReflInter,
    fun A B => rc18_card_box_le_boxSupp A B,
    rc18_familyBKR_false⟩

end StatMech.Walls
