/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Code.Walls.rc4_core

open Finset
open scoped StatMech

namespace StatMech.Walls

open StatMech ConfigSpace











theorem rc5_filter_card_congr {E F : Type*} [Fintype E] [Fintype F] (g : E ≃ F)
    (P : E → Prop) [DecidablePred P] [DecidablePred (fun y => P (g.symm y))] :
    #(univ.filter P) = #(univ.filter (fun y => P (g.symm y))) :=
  rc4_filter_card_congr g P










theorem rc5_compl_cfgEquiv {E F : Type*} (e : E ≃ F) (ωf : ConfigSpace F) :
    rmr_compl (cfgEquiv e ωf) = cfgEquiv e (rmr_compl ωf) := by
  funext a; simp only [rmr_compl_apply, cfgEquiv_apply]

















theorem rc5_reindexTransfer (hcard : ReimerCardFormAll)
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
    rw [rc5_filter_card_congr (cfgEquiv e).symm
      (fun ω : ConfigSpace β => ω ∈ disjointOccurrence A B)]
    refine congrArg Finset.card (Finset.filter_congr (fun ωf _ => ?_))
    simp only [Equiv.symm_symm]
    rw [show (cfgEquiv e ωf ∈ disjointOccurrence A B)
        ↔ ωf ∈ (cfgEquiv e) ⁻¹' (disjointOccurrence A B) from Iff.rfl,
      preimage_disjointOccurrence e A B]
  
  have hRHS : #(univ.filter (fun ω : ConfigSpace β => ω ∈ A ∧ (fun a => !ω a) ∈ B))
      = #(univ.filter (fun ωf : ConfigSpace (Fin m) => ωf ∈ A' ∧ (fun a => !ωf a) ∈ B')) := by
    rw [rc5_filter_card_congr (cfgEquiv e).symm
      (fun ω : ConfigSpace β => ω ∈ A ∧ (fun a => !ω a) ∈ B)]
    refine congrArg Finset.card (Finset.filter_congr (fun ωf _ => ?_))
    simp only [Equiv.symm_symm, hA', hB', Set.mem_preimage]
    
    constructor
    · rintro ⟨hAmem, hBmem⟩
      refine ⟨hAmem, ?_⟩
      have hc : (fun a => !(cfgEquiv e ωf) a) = cfgEquiv e (fun a => !ωf a) := by
        funext a; simp only [cfgEquiv_apply]
      rwa [hc] at hBmem
    · rintro ⟨hAmem, hBmem⟩
      refine ⟨hAmem, ?_⟩
      have hc : (fun a => !(cfgEquiv e ωf) a) = cfgEquiv e (fun a => !ωf a) := by
        funext a; simp only [cfgEquiv_apply]
      rwa [hc]
  rw [hLHS, hRHS]
  exact hbox







open Classical in




theorem rc5_reindexTransfer_inter (hcard : ReimerCardFormAll)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    #(univ.filter (fun ω : ConfigSpace β => ω ∈ disjointOccurrence A B))
      ≤ #(univ.filter (fun ω : ConfigSpace β => ω ∈ A ∩ rmr_reflect B)) :=
  (rmr_reimerCardForm_iff_inter A B).mp (rc5_reindexTransfer hcard A B)

end StatMech.Walls
