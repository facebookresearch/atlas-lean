/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Code.Walls.rc4_occursrestrictwitness
import Code.Walls.rc4_keyflipiscompl
import Code.Walls.rc4_slabdifferkey
import Code.Walls.rc4_restrictdisjoint
import Code.Walls.rc3_slabcardiffperkey
import Code.Inequalities.BK

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]













theorem rc4_filter_card_congr {E F : Type*} [Fintype E] [Fintype F] (g : E ≃ F)
    (P : E → Prop) [DecidablePred P] [DecidablePred (fun y => P (g.symm y))] :
    #(univ.filter P) = #(univ.filter (fun y => P (g.symm y))) := by
  apply Finset.card_bij (fun a _ => g a)
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rwa [Equiv.symm_apply_apply]
  · intro a _ b _ h; exact g.injective h
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    exact ⟨g.symm b, by simp only [mem_filter, mem_univ, true_and]; exact hb,
      by rw [Equiv.apply_symm_apply]⟩



theorem rc4_compl_cfgEquiv {E F : Type*} (e : E ≃ F) (ωf : ConfigSpace F) :
    (fun a => !(cfgEquiv e ωf a)) = cfgEquiv e (fun y => !ωf y) := by
  funext a; simp only [cfgEquiv_apply]






theorem rc4_reimerCardForm_transfer (hcard : ReimerCardFormAll)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    poc_ReimerCardForm A B := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivFin β
  set m := Fintype.card β with hm
  set A' : Set (ConfigSpace (Fin m)) := (cfgEquiv e) ⁻¹' A with hA'
  set B' : Set (ConfigSpace (Fin m)) := (cfgEquiv e) ⁻¹' B with hB'
  have hbox := hcard m A' B'
  unfold poc_ReimerCardForm at hbox ⊢
  have hLHS : #(univ.filter (fun ω : ConfigSpace β => ω ∈ disjointOccurrence A B))
      = #(univ.filter (fun ωf : ConfigSpace (Fin m) => ωf ∈ disjointOccurrence A' B')) := by
    rw [rc4_filter_card_congr (cfgEquiv e).symm
      (fun ω : ConfigSpace β => ω ∈ disjointOccurrence A B)]
    congr 1
    apply Finset.filter_congr
    intro ωf _
    simp only [Equiv.symm_symm]
    rw [show (cfgEquiv e ωf ∈ disjointOccurrence A B)
        ↔ ωf ∈ (cfgEquiv e) ⁻¹' (disjointOccurrence A B) from Iff.rfl,
      preimage_disjointOccurrence e A B]
  have hRHS : #(univ.filter (fun ω : ConfigSpace β => ω ∈ A ∧ (fun a => !ω a) ∈ B))
      = #(univ.filter (fun ωf : ConfigSpace (Fin m) => ωf ∈ A' ∧ (fun a => !ωf a) ∈ B')) := by
    rw [rc4_filter_card_congr (cfgEquiv e).symm
      (fun ω : ConfigSpace β => ω ∈ A ∧ (fun a => !ω a) ∈ B)]
    congr 1
  rw [hLHS, hRHS]
  exact hbox









omit [Fintype α] [DecidableEq α] in



theorem rc4_unrestrict_restrict_of_slab {k : ConfigSpace α × ConfigSpace α}
    {ω : ConfigSpace α} (hω : ω ∈ rc2_slab k) :
    pocUnrestrict k (pocRestrict k ω) = ω := by
  funext a
  by_cases h : k.1 a ≠ k.2 a
  · rw [pocUnrestrict_apply_differ k _ h]; rfl
  · rw [not_ne_iff] at h
    rw [pocUnrestrict_apply_nondiffer k _ h]
    exact (rc3_core_slab_frozen hω a h).symm

omit [Fintype α] [DecidableEq α] in




theorem rc4_keyFlip_eq_unrestrict_compl_of_slab {k : ConfigSpace α × ConfigSpace α}
    {ω : ConfigSpace α} (hω : ω ∈ rc2_slab k) :
    poc_keyFlip k ω = pocUnrestrict k (rmr_compl (pocRestrict k ω)) := by
  funext a
  by_cases h : k.1 a ≠ k.2 a
  · rw [pocUnrestrict_apply_differ k _ h, rc4_keyFlip_eq_not_on_differ k ω a h]
    simp only [rmr_compl_apply, pocRestrict_apply]
  · rw [not_ne_iff] at h
    rw [pocUnrestrict_apply_nondiffer k _ h, rc4_keyFlip_eq_id_off_differ k ω a h]
    exact rc3_core_slab_frozen hω a h

omit [Fintype α] [DecidableEq α] in




theorem rc4_unrestrict_mem_slab {k : ConfigSpace α × ConfigSpace α}
    (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false))
    (σ : ConfigSpace (DifferSub k)) : pocUnrestrict k σ ∈ rc2_slab k := by
  apply rc3_core_slab_of_frozen hvalid
  intro a hne
  exact pocUnrestrict_apply_nondiffer k σ hne










open Classical in




theorem rc4_rhs_card (k : ConfigSpace α × ConfigSpace α)
    (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false))
    (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α =>
        ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k))
      = #(univ.filter (fun σ : ConfigSpace (DifferSub k) =>
        σ ∈ pocFrozenRestrict k A ∧ (fun a => !σ a) ∈ pocFrozenRestrict k B)) := by
  apply Finset.card_bij (fun ω _ => pocRestrict k ω)
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and, Set.mem_inter_iff,
      rc2_mem_keyReflect] at hω ⊢
    obtain ⟨⟨hA, hrefl⟩, hslab⟩ := hω
    constructor
    · rw [mem_pocFrozenRestrict, rc4_unrestrict_restrict_of_slab hslab]; exact hA
    · rw [mem_pocFrozenRestrict]
      rw [show (fun a => !pocRestrict k ω a) = rmr_compl (pocRestrict k ω) from rfl,
        ← rc4_keyFlip_eq_unrestrict_compl_of_slab hslab]
      exact hrefl
  · intro ω hω ω' hω' heq
    simp only [mem_filter, mem_univ, true_and] at hω hω'
    rw [← rc4_unrestrict_restrict_of_slab hω.2, ← rc4_unrestrict_restrict_of_slab hω'.2, heq]
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    obtain ⟨hA, hB⟩ := hσ
    refine ⟨pocUnrestrict k σ, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and, Set.mem_inter_iff, rc2_mem_keyReflect]
      have hslab := rc4_unrestrict_mem_slab hvalid σ
      refine ⟨⟨?_, ?_⟩, hslab⟩
      · rw [mem_pocFrozenRestrict] at hA; exact hA
      · rw [rc4_keyFlip_eq_unrestrict_compl_of_slab hslab, pocRestrict_pocUnrestrict]
        rw [mem_pocFrozenRestrict] at hB
        rw [show rmr_compl σ = (fun a => !σ a) from rfl]; exact hB
    · exact pocRestrict_pocUnrestrict k σ










omit [Fintype α] [DecidableEq α] in



theorem rc4_pocRestrictWitness_disjoint {k : ConfigSpace α × ConfigSpace α}
    {K L : Set α} (h : Disjoint K L) :
    Disjoint (pocRestrictWitness k K) (pocRestrictWitness k L) := by
  rw [Set.disjoint_left] at h ⊢
  intro s hsK hsL
  rw [mem_pocRestrictWitness] at hsK hsL
  exact h hsK hsL

omit [Fintype α] [DecidableEq α] in




theorem rc4_box_restrict_mem {k : ConfigSpace α × ConfigSpace α}
    {A B : Set (ConfigSpace α)} {ω : ConfigSpace α}
    (hslab : ω ∈ rc2_slab k) (hbox : ω ∈ disjointOccurrence A B) :
    pocRestrict k ω ∈
      disjointOccurrence (pocFrozenRestrict k A) (pocFrozenRestrict k B) := by
  rw [mem_disjointOccurrence] at hbox ⊢
  obtain ⟨K, L, hKL, hA, hB⟩ := hbox
  refine ⟨pocRestrictWitness k K, pocRestrictWitness k L,
    rc4_pocRestrictWitness_disjoint hKL, ?_, ?_⟩
  · exact rc4_occurs_restrict_witness hslab hA
  · exact rc4_occurs_restrict_witness hslab hB

open Classical in




theorem rc4_lhs_le (k : ConfigSpace α × ConfigSpace α)
    (A B : Set (ConfigSpace α)) :
    #(univ.filter (fun ω : ConfigSpace α =>
        ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k))
      ≤ #(univ.filter (fun σ : ConfigSpace (DifferSub k) =>
        σ ∈ disjointOccurrence (pocFrozenRestrict k A) (pocFrozenRestrict k B))) := by
  apply Finset.card_le_card_of_injOn (fun ω => pocRestrict k ω)
  · intro ω hω
    rw [Finset.mem_coe, Finset.mem_filter] at hω
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact rc4_box_restrict_mem hω.2.2 hω.2.1
  · intro ω hω ω' hω' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hω hω'
    simp only at heq
    rw [← rc4_unrestrict_restrict_of_slab hω.2.2, ← rc4_unrestrict_restrict_of_slab hω'.2.2, heq]












open Classical in







theorem rc4_perKey_of_reimerCardFormAll (hcard : ReimerCardFormAll)
    (A B : Set (ConfigSpace α)) {k : ConfigSpace α × ConfigSpace α}
    (hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false)) :
    rc3_PerKey A B k := by
  have hmid : poc_ReimerCardForm (pocFrozenRestrict k A) (pocFrozenRestrict k B) :=
    rc4_reimerCardForm_transfer hcard _ _
  unfold poc_ReimerCardForm at hmid
  unfold rc3_PerKey
  calc #(univ.filter (fun ω : ConfigSpace α =>
            ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k))
      ≤ #(univ.filter (fun σ : ConfigSpace (DifferSub k) =>
            σ ∈ disjointOccurrence (pocFrozenRestrict k A) (pocFrozenRestrict k B))) :=
        rc4_lhs_le k A B
    _ ≤ #(univ.filter (fun σ : ConfigSpace (DifferSub k) =>
            σ ∈ pocFrozenRestrict k A ∧ (fun a => !σ a) ∈ pocFrozenRestrict k B)) := hmid
    _ = #(univ.filter (fun ω : ConfigSpace α =>
            ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)) :=
        (rc4_rhs_card k hvalid A B).symm









open Classical in






theorem rc4_perKey_all_of_reimerCardFormAll (hcard : ReimerCardFormAll)
    (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    rc3_PerKey A B k := by
  by_cases hvalid : ∀ a, k.1 a ≠ k.2 a → (k.1 a = true ∧ k.2 a = false)
  · exact rc4_perKey_of_reimerCardFormAll hcard A B hvalid
  · 
    have hslabempty : ∀ ω : ConfigSpace α, ω ∉ rc2_slab k := by
      intro ω hω
      exact hvalid (fun a hne => rc3_core_slab_differ_key hω a hne)
    unfold rc3_PerKey
    have hL : (univ.filter (fun ω : ConfigSpace α =>
        ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro ω _ ⟨_, hs⟩
      exact hslabempty ω hs
    have hR : (univ.filter (fun ω : ConfigSpace α =>
        ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro ω _ ⟨_, hs⟩
      exact hslabempty ω hs
    rw [hL, hR]






theorem rc4_reimerSubcubeReduction : ReimerSubcubeReduction := by
  intro hcard n A B k
  exact rc4_perKey_all_of_reimerCardFormAll hcard A B k











theorem rc4_residue_of_reimerCardFormAll (hcard : ReimerCardFormAll) : ReimerResidue :=
  rc3_core_residue_of_subcubeReduction rc4_reimerSubcubeReduction hcard



theorem rc4_perKeyAll_of_reimerCardFormAll (hcard : ReimerCardFormAll) : rc3_PerKeyAll :=
  rc4_reimerSubcubeReduction hcard

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem rc4_reimer_inequality_of_reimerCardFormAll (hcard : ReimerCardFormAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc3_core_reimer_inequality_of_subcubeReduction rc4_reimerSubcubeReduction hcard hp A B















theorem rc4_residue_iff_reimerCardFormAll : ReimerResidue ↔ ReimerCardFormAll :=
  ⟨rc3_core_reimerCardFormAll_of_residue, rc4_residue_of_reimerCardFormAll⟩

end StatMech.Walls
