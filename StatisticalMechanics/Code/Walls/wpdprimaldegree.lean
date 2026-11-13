/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.CrossingParity
import Code.Lattice.WindingWitness
import Code.Walls.wndwinding
import Code.Walls.wnuupperhalf
import Code.Walls.wnaalternate
import Code.Walls.wcbcolumnbridge
import Code.Walls.wstsigntoggle
import Code.Walls.rpccrossflip
import Code.Walls.wisindicatorsteps
import Code.Walls.wosorientedsign
import Code.Walls.welenterleave
import Code.Walls.woborientbridge

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice

open StatMech.Walls






theorem wpd_signStep_up_iff (z u v : Site 2) :
    wnd_signStep z u v = 1 ↔ (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1 := by
  classical
  unfold wnd_signStep
  constructor
  · intro h
    split_ifs at h with h1 h2 <;> first | exact h1 | (exfalso; revert h; decide)
  · intro h; simp only [if_pos h]




theorem wpd_signStep_down_iff (z u v : Site 2) :
    wnd_signStep z u v = -1 ↔ (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1 := by
  classical
  unfold wnd_signStep
  constructor
  · intro h
    split_ifs at h with h1 h2
    exact h2
  · intro h
    by_cases hup : (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1
    · exfalso
      obtain ⟨_, hu1, _⟩ := hup
      obtain ⟨_, hu1', _⟩ := h
      rw [hu1'] at hu1; omega
    · simp only [if_neg hup, if_pos h]


theorem wpd_signStep_dichotomy (z u v : Site 2) (h : wnd_signStep z u v ≠ 0) :
    ((u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1) ∨
    ((u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1) := by
  rcases wnd_signStep_mem z u v with h1 | h1 | h1
  · exact Or.inl ((wpd_signStep_up_iff z u v).mp h1)
  · exact absurd h1 h
  · exact Or.inr ((wpd_signStep_down_iff z u v).mp h1)










theorem wpd_count_le_one_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) (e : Sym2 (Site 2)) :
    Vc.edges.count e ≤ 1 := by
  exact List.nodup_iff_count_le_one.mp hnd e



theorem wpd_simple_cross_le_one {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (z : Site 2) (c : ℤ) :
    Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)) ≤ 1 :=
  wpd_count_le_one_of_nodup Vc hcyc.edges_nodup _





theorem wpd_simple_cross_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (z : Site 2) (c : ℤ) :
    wis_ind z Vc (c + 1) ≠ wis_ind z Vc c ↔
      Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)) = 1 := by
  rw [wis_ind_step_neq_iff z Vc c]
  constructor
  · intro hodd
    have hle := wpd_simple_cross_le_one Vc hcyc z c
    rw [Nat.odd_iff] at hodd
    omega
  · intro h1; rw [h1]; exact odd_one





















def wpd_UpEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  wel_OrientationConsistent z Vc


theorem wpd_upEntersInterior_iff_orientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    wpd_UpEntersInterior z Vc ↔ wel_OrientationConsistent z Vc := Iff.rfl




theorem wpd_orientationConsistent_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc) :
    wel_OrientationConsistent z Vc := h




theorem wpd_signsAlternate_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc) :
    wos_SignsAlternateInColumnOrder z Vc :=
  wel_signsAlternate_of_orientationConsistent z Vc h



theorem wpd_columnAlternates_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc) :
    wna_ColumnAlternates z Vc :=
  wel_columnAlternates_of_orientationConsistent z Vc h





theorem wpd_signedCross_pm_one_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc)
    (hodd : ¬ Even (jec_rayCount z Vc)) :
    wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 :=
  wel_signedCross_pm_one z Vc h hodd






















theorem wpd_upEntersInterior_of_alternate (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (halt : wos_SignsAlternateInColumnOrder z Vc)
    (hlen : wos_IndicatorLenEq z Vc) :
    wpd_UpEntersInterior z Vc := by
  obtain ⟨c₀, N, hbase, hlenEq⟩ := hlen
  refine ⟨c₀, N, hbase, ?_⟩
  set D := wis_nonzeroDiffs (wis_indSeq z Vc c₀) N with hD
  have hDalt : wnu_Alt D := wos_indNonzeroDiffs_alternates z Vc c₀ N hbase
  have hCalt : wnu_Alt (wcb_columnSorted z Vc) := halt
  by_cases hlenz : (wcb_columnSorted z Vc).length = 0
  · 
    have hDempty : D = [] := List.length_eq_zero_iff.mp (by rw [hlenEq, hlenz])
    have hCempty : wcb_columnSorted z Vc = [] := List.length_eq_zero_iff.mp hlenz
    exact Or.inl (by rw [hCempty, hDempty])
  · have hDne : D ≠ [] := by intro h; apply hlenz; rw [← hlenEq, h]; simp
    have hCne : wcb_columnSorted z Vc ≠ [] := fun h => hlenz (by rw [h]; simp)
    have hDhead : D.headI = 1 :=
      wos_nonzeroDiffs_head_one (wis_indSeq z Vc c₀)
        (fun m => wis_indSeq_in_01 z Vc c₀ m) hbase N hDne
    have hChead : (wcb_columnSorted z Vc).headI = 1 ∨ (wcb_columnSorted z Vc).headI = -1 := by
      obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hCne
      have := wnu_Alt_head_pm (hct ▸ hCalt)
      rw [hct]; simpa using this
    rcases hChead with hCp | hCm
    · 
      left
      exact (wos_alt_eq_of_len_head hCalt hDalt hlenEq.symm (by rw [hCp, hDhead]))
    · 
      right
      apply wos_alt_eq_of_len_head hCalt (wos_alt_map_neg hDalt)
      · simp [hlenEq]
      · obtain ⟨d, t, hdt⟩ := List.exists_cons_of_ne_nil hDne
        have hd1 : d = 1 := by rw [← hDhead, hdt]; rfl
        rw [hCm, hdt, List.map_cons]
        simp only [List.headI, hd1]





theorem wpd_upEntersInterior_iff_alternate_and_len (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    wpd_UpEntersInterior z Vc ↔
      (wos_SignsAlternateInColumnOrder z Vc ∧ wos_IndicatorLenEq z Vc) := by
  constructor
  · intro h
    refine ⟨wpd_signsAlternate_of_upEntersInterior z Vc h, ?_⟩
    
    obtain ⟨c₀, N, hbase, hbranch⟩ := h
    refine ⟨c₀, N, hbase, ?_⟩
    rcases hbranch with hEq | hEqNeg
    · rw [hEq]
    · rw [hEqNeg]; simp
  · rintro ⟨halt, hlen⟩; exact wpd_upEntersInterior_of_alternate z Vc halt hlen






theorem wpd_unitSquare_upEntersInterior :
    wpd_UpEntersInterior (![1, 1] : Site 2) wwit_unitSquareLoop :=
  (wob_columnSortedEqJumps_iff_orientationConsistent _ _).mp wob_unitSquare_columnSortedEqJumps



theorem wpd_Ltromino_upEntersInterior :
    wpd_UpEntersInterior (![1, 1] : Site 2) wnu_LtrominoLoop :=
  (wob_columnSortedEqJumps_iff_orientationConsistent _ _).mp wob_Ltromino_columnSortedEqJumps












theorem wpd_doubleSquare_not_upEntersInterior :
    ¬ wpd_UpEntersInterior (![1, 1] : Site 2) wnu_doubleSquare :=
  wel_doubleSquare_not_orientationConsistent

end Lattice

end StatMech
