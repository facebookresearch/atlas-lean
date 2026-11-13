/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































































import Mathlib
import Code.Walls.gc30reroute
import Code.Ising.BackboneResummation
import Code.Ising.BackboneExists
import Code.Ising.HdomMultiplicity
import Code.Walls.gc7ghosteven

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



















theorem gc31_flux_monotone_not_noneConn (Ψ : Sharpness.Current V → Sharpness.Current V)
    (m : Sharpness.Current V) {o x y : V}
    (hmono : ∀ e, m e ≤ Ψ m e)
    (hall : hnw_allConn G m o x y) :
    ¬ hnw_noneConn G (Ψ m) o x y := by
  obtain ⟨hxy', _, _⟩ := hall
  intro hnone
  apply hnone.1
  refine connP_mono (Q := posEdges G.edgeFinset (Ψ m)) ?_ (connOdd_imp_connPos G.edgeFinset m hxy')
  intro e he
  rw [posEdges, Finset.mem_filter] at he ⊢
  exact ⟨he.1, le_trans he.2 (hmono e)⟩




theorem gc31_addBackbone_not_noneConn (m : Sharpness.Current V) (P : Finset (Sym2 V))
    {o x y : V} (hall : hnw_allConn G m o x y) :
    ¬ hnw_noneConn G (hmu_addBackbone P m) o x y :=
  gc31_flux_monotone_not_noneConn G (fun m' => hmu_addBackbone P m') m
    (fun e => by simp only [hmu_addBackbone_apply]; omega) hall



















def gc31_MassDoublingSurgery (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (B : Finset V) (o x y : V) : Prop :=
  ∃ Φ : Sharpness.Current V → Sharpness.Current V,
    (∀ m ∈ bbr_allFilter G M o x y, Φ m ∈ bbr_noneFilter G M o x y)
    ∧ (Set.InjOn Φ (bbr_allFilter G M o x y))
    ∧ (∀ m ∈ bbr_allFilter G M o x y, 2 * hnw_mass G β J m B ≤ hnw_mass G β J (Φ m) B)





theorem gc31_backboneSurgery_of_massDoubling (β : ℝ) (J : Sym2 V → ℝ)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (h : gc31_MassDoublingSurgery G β J M B o x y) :
    bbr_BackboneSurgery G β J M B o x y := by
  obtain ⟨Φ, hmem, hinj, hbound⟩ := h
  exact ⟨Φ, hmem, fun a ha a' ha' => hinj ha ha', hbound⟩






theorem gc31_native_gap_nonneg_of_massDoubling (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (h : gc31_MassDoublingSurgery G β J M B o x y) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y :=
  gc30_native_gap_nonneg_of_backboneSurgery G β J hβ hJ M hnd B hm hox hoy hxy hcoh
    (gc31_backboneSurgery_of_massDoubling G β J M B o x y h)













theorem gc31_massDoubling_of_singleton_dominated (β : ℝ) (J : Sym2 V → ℝ)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (ma mstar : Sharpness.Current V)
    (hsingle : bbr_allFilter G M o x y = {ma})
    (hstar : mstar ∈ bbr_noneFilter G M o x y)
    (hdom : 2 * hnw_mass G β J ma B ≤ hnw_mass G β J mstar B) :
    gc31_MassDoublingSurgery G β J M B o x y := by
  refine ⟨fun _ => mstar, ?_, ?_, ?_⟩
  · intro m hm; exact hstar
  · intro a ha a' ha' _
    rw [hsingle, Finset.coe_singleton, Set.mem_singleton_iff] at ha ha'
    rw [ha, ha']
  · intro m hm
    rw [hsingle, Finset.mem_singleton] at hm
    rw [hm]; exact hdom














theorem gc31_mass_zero_of_odd_card (β : ℝ) (J : Sym2 V → ℝ) (m : Sharpness.Current V)
    (S : Finset V) (hodd : ¬ Even S.card) :
    hnw_mass G β J m S = 0 := by
  unfold hnw_mass splitWeightedSum
  apply Finset.sum_eq_zero
  intro K _
  rw [if_neg]
  intro hK
  exact hodd (hK ▸ gc7_sources_card_even G K.1)




theorem gc31_connP_empty_eq {a b : V} (h : connP (∅ : Finset (Sym2 V)) a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hstep _ => obtain ⟨e, he, _, _, _⟩ := hstep; exact absurd he (Finset.notMem_empty e)


def gc31_zeroM : Sharpness.Current (Fin 3) := fun _ => 0



theorem gc31_zero_noneConn : hnw_noneConn hmu_TriG gc31_zeroM 0 1 2 := by
  have hpos : posEdges hmu_TriG.edgeFinset gc31_zeroM = ∅ := by
    unfold posEdges gc31_zeroM
    apply Finset.filter_false_of_mem
    intro e _; simp
  rw [hnw_noneConn, hpos]
  refine ⟨?_, ?_, ?_⟩ <;> · intro h; have := gc31_connP_empty_eq h; simp at this





theorem gc31_allFilter_witness :
    bbr_allFilter hmu_TriG ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) 0 1 2
      = {hmu_triM} := by
  unfold bbr_allFilter
  ext m
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hall⟩
    rcases hmem with rfl | rfl
    · rfl
    · exact absurd hall (hnw_noneConn_not_allConn hmu_TriG gc31_zeroM gc31_zero_noneConn)
  · rintro rfl
    exact ⟨Or.inl rfl, hmu_tri_allConn⟩


theorem gc31_zero_in_noneFilter :
    gc31_zeroM ∈ bbr_noneFilter hmu_TriG
      ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) 0 1 2 := by
  unfold bbr_noneFilter
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), gc31_zero_noneConn⟩















theorem gc31_massDoubling_witness :
    gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1)
      ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) ({0} : Finset (Fin 3)) 0 1 2 := by
  have hodd : ¬ Even ({0} : Finset (Fin 3)).card := by decide
  refine gc31_massDoubling_of_singleton_dominated hmu_TriG 1 (fun _ => 1) _ _ 0 1 2
    hmu_triM gc31_zeroM gc31_allFilter_witness gc31_zero_in_noneFilter ?_
  rw [gc31_mass_zero_of_odd_card hmu_TriG 1 (fun _ => 1) hmu_triM _ hodd,
      gc31_mass_zero_of_odd_card hmu_TriG 1 (fun _ => 1) gc31_zeroM _ hodd]
  norm_num







theorem gc31_backboneSurgery_witness :
    bbr_BackboneSurgery hmu_TriG 1 (fun _ => 1)
      ({hmu_triM, gc31_zeroM} : Finset (Sharpness.Current (Fin 3))) ({0} : Finset (Fin 3)) 0 1 2 :=
  gc31_backboneSurgery_of_massDoubling hmu_TriG 1 (fun _ => 1) _ _ 0 1 2 gc31_massDoubling_witness



















theorem gc31_massDoubling_fails_triangle_emptyB :
    ¬ gc31_MassDoublingSurgery hmu_TriG 1 (fun _ => 1)
        ({hmu_triM} : Finset (Sharpness.Current (Fin 3))) (∅ : Finset (Fin 3)) 0 1 2 := by
  intro h
  exact hmu_hdom_refutable
    (bbr_hdom_of_surgery hmu_TriG 1 (fun _ => 1) (by norm_num) (fun _ => by norm_num) _ ∅ 0 1 2
      (gc31_backboneSurgery_of_massDoubling hmu_TriG 1 (fun _ => 1) _ ∅ 0 1 2 h))

end StatMech.Walls
