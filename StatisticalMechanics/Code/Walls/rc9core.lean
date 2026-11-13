/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Code.Walls.rc8core
import Code.Inequalities.Reimer

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









omit [Fintype α] [DecidableEq α] in

theorem rc9_flipCfg_eq_compl (ω : ConfigSpace α) : flipCfg ω = rmr_compl ω := rfl

omit [Fintype α] [DecidableEq α] in

theorem rc9_flip_preimage_involutive (A : Set (ConfigSpace α)) :
    flipCfg ⁻¹' (flipCfg ⁻¹' A) = A := by
  ext ω; simp only [Set.mem_preimage, flipCfg_flipCfg]

omit [Fintype α] [DecidableEq α] in


theorem rc9_isDecreasing_flip_preimage {A : Set (ConfigSpace α)} (hA : IsIncreasing A) :
    IsDecreasing (flipCfg ⁻¹' A) := by
  intro ω ω' hωω' hω
  simp only [Set.mem_preimage] at hω ⊢
  exact hA (flipCfg_antitone hωω') hω













lemma rc9_card_flip_eq {S' S : Set (ConfigSpace α)} [DecidablePred (· ∈ S')]
    [DecidablePred (· ∈ S)] (h : ∀ ω, ω ∈ S' ↔ flipCfg ω ∈ S) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ S'))
      = #(univ.filter (fun ω : ConfigSpace α => ω ∈ S)) := by
  apply Finset.card_bij (fun ω _ => flipCfg ω)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact (h ω).mp hω
  · intro a _ b _ hab
    have := congrArg flipCfg hab
    rwa [flipCfg_flipCfg, flipCfg_flipCfg] at this
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ⟨flipCfg ω, by rw [h, flipCfg_flipCfg]; exact hω, by rw [flipCfg_flipCfg]⟩

omit [Fintype α] [DecidableEq α] in



lemma rc9_rhs_flip_iff (A B : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ω ∈ (flipCfg ⁻¹' A) ∩ rmr_reflect (flipCfg ⁻¹' B) ↔ flipCfg ω ∈ A ∩ rmr_reflect B := by
  have h1 : flipCfg (rmr_compl ω) = ω := by funext a; simp [flipCfg, rmr_compl]
  have h2 : rmr_compl (flipCfg ω) = ω := by funext a; simp [flipCfg, rmr_compl]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨hA, ?_⟩
    rw [rmr_mem_reflect, h2]; rw [rmr_mem_reflect, Set.mem_preimage, h1] at hB; exact hB
  · rintro ⟨hA, hB⟩
    refine ⟨hA, ?_⟩
    rw [rmr_mem_reflect, Set.mem_preimage, h1]; rw [rmr_mem_reflect, h2] at hB; exact hB

omit [Fintype α] [DecidableEq α] in



lemma rc9_box_flip_iff (A B : Set (ConfigSpace α)) (ω : ConfigSpace α) :
    ω ∈ disjointOccurrence (flipCfg ⁻¹' A) (flipCfg ⁻¹' B)
      ↔ flipCfg ω ∈ disjointOccurrence A B := by
  rw [← preimage_flip_disjointOccurrence A B]; rfl

open Classical in




theorem rc9_deficit_flip_invariant (A B : Set (ConfigSpace α)) :
    rc5_deficit (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) = rc5_deficit A B := by
  unfold rc5_deficit
  congr 1
  · exact_mod_cast rc9_card_flip_eq (rc9_box_flip_iff A B)
  · exact_mod_cast rc9_card_flip_eq (rc9_rhs_flip_iff A B)



theorem rc9_deficit_le_of_flip {A B : Set (ConfigSpace α)}
    (h : rc5_deficit (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) ≤ 0) : rc5_deficit A B ≤ 0 := by
  rwa [rc9_deficit_flip_invariant] at h







open Classical in



lemma rc9_card_compl_swap (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α => ω ∈ B ∩ rmr_reflect A))
      = #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  apply Finset.card_bij (fun ω _ => rmr_compl ω)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      rmr_mem_reflect, rmr_compl_compl] at hω ⊢
    exact ⟨hω.2, hω.1⟩
  · intro a _ b _ hab; exact rmr_compl_injective hab
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      rmr_mem_reflect] at hω ⊢
    refine ⟨rmr_compl ω, ⟨?_, ?_⟩, rmr_compl_compl ω⟩
    · exact hω.2
    · rw [rmr_compl_compl]; exact hω.1

open Classical in



theorem rc9_deficit_swap (A B : Set (ConfigSpace α)) :
    rc5_deficit A B = rc5_deficit B A := by
  unfold rc5_deficit
  congr 1
  · rw [disjointOccurrence_comm A B]
  · exact_mod_cast (rc9_card_compl_swap A B).symm


theorem rc9_deficit_le_swap {A B : Set (ConfigSpace α)} (h : rc5_deficit A B ≤ 0) :
    rc5_deficit B A ≤ 0 := by rwa [rc9_deficit_swap] at h











theorem rc9_decDec_of_incInc
    (hII : ∀ {A B : Set (ConfigSpace α)}, IsIncreasing A → IsIncreasing B → rc5_deficit A B ≤ 0)
    {A B : Set (ConfigSpace α)} (hA : IsDecreasing A) (hB : IsDecreasing B) :
    rc5_deficit A B ≤ 0 := by
  have := hII (isIncreasing_flip_preimage hA) (isIncreasing_flip_preimage hB)
  rwa [rc9_deficit_flip_invariant] at this















def rc9_DeficitBridgeResidue : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
    ¬ ((IsIncreasing A ∧ IsDecreasing B) ∨ (IsDecreasing A ∧ IsIncreasing B)) →
    ¬ (IsDecreasing A ∧ IsDecreasing B) →
      rc5_deficit A B ≤ 0







theorem rc9_deficitBridge_of_residue (h : rc9_DeficitBridgeResidue) : rc7_DeficitBridge := by
  intro n A B
  by_cases hopp : (IsIncreasing A ∧ IsDecreasing B) ∨ (IsDecreasing A ∧ IsIncreasing B)
  · rcases hopp with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact rc8_deficit_le_zero_inc_dec hA hB
    · exact rc8_deficit_le_zero_dec_inc hA hB
  · by_cases hdd : IsDecreasing A ∧ IsDecreasing B
    · 
      apply rc9_deficit_le_of_flip
      set A' := flipCfg ⁻¹' A with hA'def
      set B' := flipCfg ⁻¹' B with hB'def
      have hA' : IsIncreasing A' := isIncreasing_flip_preimage hdd.1
      have hB' : IsIncreasing B' := isIncreasing_flip_preimage hdd.2
      by_cases hopp' : (IsIncreasing A' ∧ IsDecreasing B') ∨ (IsDecreasing A' ∧ IsIncreasing B')
      · rcases hopp' with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact rc8_deficit_le_zero_inc_dec ha hb
        · exact rc8_deficit_le_zero_dec_inc ha hb
      · by_cases hdd' : IsDecreasing A' ∧ IsDecreasing B'
        · exact absurd (Or.inl ⟨hA', hdd'.2⟩) hopp'
        · exact h n A' B' hopp' hdd'
    · exact h n A B hopp hdd



theorem rc9_residue_of_deficitBridge (h : rc7_DeficitBridge) : rc9_DeficitBridgeResidue :=
  fun n A B _ _ => h n A B





theorem rc9_residue_iff_deficitBridge : rc7_DeficitBridge ↔ rc9_DeficitBridgeResidue :=
  ⟨rc9_residue_of_deficitBridge, rc9_deficitBridge_of_residue⟩









theorem rc9_residue_iff_nonOpp : rc9_DeficitBridgeResidue ↔ rc8_DeficitBridgeNonOpp :=
  rc9_residue_iff_deficitBridge.symm.trans rc8_deficitBridge_iff_nonOpp



theorem rc9_reimerCardFormAll_of_residue (h : rc9_DeficitBridgeResidue) : ReimerCardFormAll :=
  rc7_reimerCardFormAll_of_deficitBridge (rc9_deficitBridge_of_residue h)










theorem rc9_deficit_swap_rbi : rc5_deficit rbi_A rbi_B = rc5_deficit rbi_B rbi_A :=
  rc9_deficit_swap rbi_A rbi_B



theorem rc9_deficit_flip_rbi :
    rc5_deficit (flipCfg ⁻¹' rbi_A) (flipCfg ⁻¹' rbi_B) = rc5_deficit rbi_A rbi_B :=
  rc9_deficit_flip_invariant rbi_A rbi_B



theorem rc9_deficit_one (A B : Set (ConfigSpace (Fin 1))) : rc5_deficit A B ≤ 0 :=
  rc7_deficit_one A B



theorem rc9_deficit_rbi : rc5_deficit rbi_A rbi_B ≤ 0 :=
  rc7_deficit_rbi
























theorem rc9_cardform_symmetry_reduction :
    (∀ A B : Set (ConfigSpace α),
        rc5_deficit (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) = rc5_deficit A B)
      ∧ (∀ A B : Set (ConfigSpace α), rc5_deficit A B = rc5_deficit B A)
      ∧ (rc7_DeficitBridge ↔ rc9_DeficitBridgeResidue)
      ∧ (rc9_DeficitBridgeResidue ↔ rc8_DeficitBridgeNonOpp)
      ∧ (rc9_DeficitBridgeResidue → ReimerCardFormAll) :=
  ⟨rc9_deficit_flip_invariant,
    rc9_deficit_swap,
    rc9_residue_iff_deficitBridge,
    rc9_residue_iff_nonOpp,
    rc9_reimerCardFormAll_of_residue⟩

end StatMech.Walls
