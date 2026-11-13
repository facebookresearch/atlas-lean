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

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice

open StatMech.Walls














theorem wel_enterLeaveAlt (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (c₀ : ℤ) (N : ℕ)
    (hbase : wis_indSeq z Vc c₀ 0 = 0) :
    wnu_Alt (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N) :=
  wos_indNonzeroDiffs_alternates z Vc c₀ N hbase





theorem wel_enterLeaveHead (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (c₀ : ℤ) (N : ℕ)
    (hbase : wis_indSeq z Vc c₀ 0 = 0)
    (hne : wis_nonzeroDiffs (wis_indSeq z Vc c₀) N ≠ []) :
    (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).headI = 1 :=
  wos_nonzeroDiffs_head_one (wis_indSeq z Vc c₀)
    (fun m => wis_indSeq_in_01 z Vc c₀ m) hbase N hne






























def wel_OrientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ (c₀ : ℤ) (N : ℕ), wis_indSeq z Vc c₀ 0 = 0 ∧
    (wcb_columnSorted z Vc = wis_nonzeroDiffs (wis_indSeq z Vc c₀) N ∨
     wcb_columnSorted z Vc =
       (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).map (fun x => -x))













theorem wel_signsAlternate_of_orientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wel_OrientationConsistent z Vc) :
    wos_SignsAlternateInColumnOrder z Vc := by
  obtain ⟨c₀, N, hbase, hbranch⟩ := h
  have hDalt : wnu_Alt (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N) :=
    wel_enterLeaveAlt z Vc c₀ N hbase
  unfold wos_SignsAlternateInColumnOrder
  rcases hbranch with hEq | hEqNeg
  · rw [hEq]; exact hDalt
  · rw [hEqNeg]; exact wos_alt_map_neg hDalt








theorem wel_signEqIndicatorJumps_of_orientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wel_OrientationConsistent z Vc) :
    wis_SignEqIndicatorJumps z Vc := by
  obtain ⟨c₀, N, hbase, hbranch⟩ := h
  have hperm : (wcb_columnSorted z Vc).Perm (wnu_signedList z Vc) :=
    wcb_columnOrder_permutes_signedList z Vc
  refine ⟨c₀, N, hbase, ?_⟩
  rcases hbranch with hEq | hEqNeg
  · left; rw [← hEq]; exact hperm
  · right
    
    have hnegList : wis_nonzeroDiffs (fun i => - wis_indSeq z Vc c₀ i) N
        = (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).map (fun x => -x) :=
      wos_nonzeroDiffs_neg (wis_indSeq z Vc c₀) N
    rw [hnegList, ← hEqNeg]; exact hperm






theorem wel_columnAlternates_of_orientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wel_OrientationConsistent z Vc) :
    wna_ColumnAlternates z Vc :=
  wos_signsAlternate_columnAlternates z Vc (wel_signsAlternate_of_orientationConsistent z Vc h)


theorem wel_signedCross_abs_le_one (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wel_OrientationConsistent z Vc) :
    |wnd_signedCross z Vc| ≤ 1 :=
  wos_signedCross_abs_le_one z Vc (wel_signsAlternate_of_orientationConsistent z Vc h)





theorem wel_signedCross_pm_one (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wel_OrientationConsistent z Vc)
    (hodd : ¬ Even (jec_rayCount z Vc)) :
    wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 :=
  wos_signedCross_pm_one z Vc (wel_signsAlternate_of_orientationConsistent z Vc h) hodd











theorem wel_doubleSquare_list_not_alternates : ¬ wnu_Alt ([1, 1] : List ℤ) := by
  intro h
  have := (wnu_Alt_cons_cons.mp h).2.1
  norm_num at this





theorem wel_doubleSquare_not_orientationConsistent :
    ¬ wel_OrientationConsistent (![1, 1] : Site 2) wnu_doubleSquare := by
  intro h
  have halt : wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wnu_doubleSquare :=
    wel_signsAlternate_of_orientationConsistent _ _ h
  unfold wos_SignsAlternateInColumnOrder at halt
  rw [wcb_doubleSquare_columnSorted] at halt
  exact wel_doubleSquare_list_not_alternates halt















theorem wel_twoToggle_bothBranches_alternate :
    wnu_Alt ([1, -1] : List ℤ) ∧ wnu_Alt (([1, -1] : List ℤ).map (fun x => -x)) := by
  refine ⟨wos_twoToggle_alternates, ?_⟩
  simpa using wos_alt_map_neg wos_twoToggle_alternates






theorem wel_unitSquare_signsAlternate_consistent :
    wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wwit_unitSquareLoop :=
  wos_unitSquare_signsAlternate

end Lattice

end StatMech
