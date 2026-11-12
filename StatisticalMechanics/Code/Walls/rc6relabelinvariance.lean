/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Code.Walls.rc6deficitform
import Code.Walls.rc5_reindextransfer

open Finset
open scoped StatMech

namespace StatMech.Walls

open StatMech ConfigSpace














theorem rc6_preimage_inter_reflect {E F : Type*} (e : E ≃ F) (A B : Set (ConfigSpace E)) :
    (cfgEquiv e) ⁻¹' (A ∩ rmr_reflect B)
      = (cfgEquiv e ⁻¹' A) ∩ rmr_reflect (cfgEquiv e ⁻¹' B) := by
  ext ωf
  simp only [Set.mem_preimage, Set.mem_inter_iff, rmr_mem_reflect, rc5_compl_cfgEquiv]


















theorem rc6_deficit_cfgEquiv_invariant {E F : Type*} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] (e : E ≃ F) (A B : Set (ConfigSpace E)) :
    rc6_deficit A B = rc6_deficit (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B) := by
  classical
  
  have hbox :
      #(univ.filter (fun ω : ConfigSpace E => ω ∈ disjointOccurrence A B))
        = #(univ.filter (fun ωf : ConfigSpace F =>
            ωf ∈ disjointOccurrence (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B))) := by
    rw [rc5_filter_card_congr (cfgEquiv e).symm
      (fun ω : ConfigSpace E => ω ∈ disjointOccurrence A B)]
    refine congrArg Finset.card (Finset.filter_congr (fun ωf _ => ?_))
    simp only [Equiv.symm_symm]
    rw [show (cfgEquiv e ωf ∈ disjointOccurrence A B)
        ↔ ωf ∈ (cfgEquiv e) ⁻¹' (disjointOccurrence A B) from Iff.rfl,
      preimage_disjointOccurrence e A B]
  
  have hint :
      #(univ.filter (fun ω : ConfigSpace E => ω ∈ A ∩ rmr_reflect B))
        = #(univ.filter (fun ωf : ConfigSpace F =>
            ωf ∈ (cfgEquiv e ⁻¹' A) ∩ rmr_reflect (cfgEquiv e ⁻¹' B))) := by
    rw [rc5_filter_card_congr (cfgEquiv e).symm
      (fun ω : ConfigSpace E => ω ∈ A ∩ rmr_reflect B)]
    refine congrArg Finset.card (Finset.filter_congr (fun ωf _ => ?_))
    simp only [Equiv.symm_symm, Set.mem_inter_iff, rmr_mem_reflect, rc5_compl_cfgEquiv,
      Set.mem_preimage]
  unfold rc6_deficit
  rw [hbox, hint]








open Classical in





theorem rc6_deficit_relabel_to_fin {β : Type*} [Fintype β] [DecidableEq β]
    (A B : Set (ConfigSpace β)) :
    ∃ (e : β ≃ Fin (Fintype.card β)),
      rc6_deficit A B = rc6_deficit (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B) := by
  obtain ⟨e⟩ := Fintype.truncEquivFin β
  exact ⟨e, rc6_deficit_cfgEquiv_invariant e A B⟩








theorem rc6_deficitNonpos_of_fin (h : rc6_DeficitNonpos)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    rc6_deficit A B ≤ 0 := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivFin β
  rw [rc6_deficit_cfgEquiv_invariant e A B]
  exact h (Fintype.card β) _ _













def rc6_DeficitNonposAllFinite : Prop :=
  ∀ (β : Type) [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)), rc6_deficit A B ≤ 0






theorem rc6_deficitNonposAllFinite_iff :
    rc6_DeficitNonposAllFinite ↔ rc6_DeficitNonpos := by
  unfold rc6_DeficitNonposAllFinite rc6_DeficitNonpos
  constructor
  · intro h n A B; exact h (Fin n) A B
  · intro h β _ _ A B; exact rc6_deficitNonpos_of_fin h A B












theorem rc6_reimerCardFormAll_iff_deficitNonposAllFinite :
    ReimerCardFormAll ↔ rc6_DeficitNonposAllFinite := by
  rw [rc6_deficitNonposAllFinite_iff, ← rc6_deficitNonpos_iff_reimerCardFormAll]






theorem rc6_reimerCardForm_of_reimerCardFormAll (hcard : ReimerCardFormAll)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    StatMech.poc_ReimerCardForm A B := by
  rw [rc6_reimerCardForm_iff_deficit]
  exact rc6_deficitNonpos_of_fin (rc6_deficitNonpos_iff_reimerCardFormAll.mpr hcard) A B





















theorem rc6_relabel_invariance :
    (∀ {E F : Type} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
        (e : E ≃ F) (A B : Set (ConfigSpace E)),
        rc6_deficit A B = rc6_deficit (cfgEquiv e ⁻¹' A) (cfgEquiv e ⁻¹' B))
      ∧ (rc6_DeficitNonposAllFinite ↔ rc6_DeficitNonpos)
      ∧ (ReimerCardFormAll ↔ rc6_DeficitNonposAllFinite) :=
  ⟨fun e A B => rc6_deficit_cfgEquiv_invariant e A B,
    rc6_deficitNonposAllFinite_iff,
    rc6_reimerCardFormAll_iff_deficitNonposAllFinite⟩

end StatMech.Walls
