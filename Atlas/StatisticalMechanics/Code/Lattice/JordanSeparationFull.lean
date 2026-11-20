/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.CornerBalance
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.BdEdgeMatchStarHull
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.MinimalPeriodLoop

open Set SimpleGraph Function

namespace StatMech

namespace Lattice


















theorem jsf_bdEdgeMatch_of_rayParity {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
    pww_BdEdgeMatch K Vc :=
  pbs_bdEdgeMatch_of_leftRegion_eq Vc (ccs_cluster_eq_leftRegion Vc hin hout)



















theorem jsf_unitCell_loop_edges :
    (mpl_orbitLoop unitCell ucBase).edges
      = [s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1]),
          s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0])] := by
  rw [mpl_orbitLoop_edges]; exact mpl_unitCell_faceLoop_edges











theorem jsf_unitCell_rayCount (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop unitCell ucBase)
      = (if z 1 = 0 ∧ 1 ≤ z 0 then 1 else 0)
        + (if z 1 = 0 ∧ 0 ≤ z 0 then 1 else 0) := by
  classical
  rw [jec_rayCount, jsf_unitCell_loop_edges]
  simp only [List.countP_cons, List.countP_nil]
  
  have h1 : decide (jec_rayEdge z s((![0, 0] : Site 2), ![0, -1]))
      = decide (z 1 = 0 ∧ 1 ≤ z 0) := by
    rw [decide_eq_decide]
    simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
    constructor
    · rintro ⟨h2, h3 | h4⟩ <;> omega
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  
  have h2 : decide (jec_rayEdge z s((![0, -1] : Site 2), ![-1, -1])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  
  have h3 : decide (jec_rayEdge z s((![-1, -1] : Site 2), ![-1, 0]))
      = decide (z 1 = 0 ∧ 0 ≤ z 0) := by
    rw [decide_eq_decide]
    simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
    constructor
    · rintro ⟨h2, h3 | h4⟩ <;> omega
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  
  have h4 : decide (jec_rayEdge z s((![-1, 0] : Site 2), ![0, 0])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  rw [h1, h2, h3, h4]
  simp only [decide_eq_true_eq, Bool.false_eq_true, if_false, add_zero, zero_add]
  exact Nat.add_comm _ _










theorem jsf_unitCell_inside_odd (z : Site 2) (hz : z ∈ unitCell) :
    ¬ Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) := by
  simp only [unitCell, Set.mem_singleton_iff] at hz
  subst hz
  rw [jsf_unitCell_rayCount]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num





theorem jsf_unitCell_outside_even (z : Site 2) (hz : z ∉ unitCell) :
    Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) := by
  rw [jsf_unitCell_rayCount]
  
  have hne : ¬ (z 0 = 0 ∧ z 1 = 0) := by
    intro ⟨h0, h1⟩
    apply hz
    simp only [unitCell, Set.mem_singleton_iff]
    funext i; fin_cases i
    · simpa using h0
    · simpa using h1
  by_cases ha : z 1 = 0 ∧ 1 ≤ z 0 <;> by_cases hb : z 1 = 0 ∧ 0 ≤ z 0
  · simp only [if_pos ha, if_pos hb]; decide
  · simp only [if_pos ha, if_neg hb]; omega
  · 
    exfalso
    obtain ⟨hb1, hb0⟩ := hb
    exact hne ⟨by omega, hb1⟩
  · simp only [if_neg ha, if_neg hb]; exact Even.zero





theorem jsf_unitCell_eq_leftRegion :
    unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) :=
  ccs_cluster_eq_leftRegion (mpl_orbitLoop unitCell ucBase)
    jsf_unitCell_inside_odd jsf_unitCell_outside_even








theorem jsf_unitCell_loop_isCycle : (mpl_orbitLoop unitCell ucBase).IsCycle := by
  have hp : 3 ≤ dartOrbitPeriod unitCell ucBase := by
    rw [unitCell_orbitPeriod_eq_four]; norm_num
  have hinj : Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
    rw [unitCell_orbitPeriod_eq_four]
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    have hbase : (ucBase).1 = ucDart0 := rfl
    rw [hbase] at hij
    interval_cases i <;> interval_cases j <;>
      first
      | rfl
      | (exfalso; revert hij;
         simp only [mpl_dartFace_iterate_ucDart0, mpl_dartFace_iterate_ucDart1,
           mpl_dartFace_iterate_ucDart2, mpl_dartFace_iterate_ucDart3];
         intro hij;
         have h0 := congrFun hij 0; have h1 := congrFun hij 1;
         simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1; omega)
  exact mpl_orbitLoop_isCycle unitCell ucBase hp hinj













theorem jsf_unitCell_bdEdgeMatch :
    pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) :=
  jsf_bdEdgeMatch_of_rayParity (mpl_orbitLoop unitCell ucBase)
    jsf_unitCell_inside_odd jsf_unitCell_outside_even












theorem jsf_unitCell_fillClosed : ndt_FillClosed unitCell := by
  refine ⟨fun f h00 h11 => ?_, fun f h10 h01 => ?_⟩
  · exfalso
    simp only [unitCell, Set.mem_singleton_iff, npd_P00, npd_P11] at h00 h11
    have e0 : f 0 = 0 := by have := congrFun h00 0; simpa using this
    have e1 : f 1 = 0 := by have := congrFun h00 1; simpa using this
    have := congrFun h11 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    omega
  · exfalso
    simp only [unitCell, Set.mem_singleton_iff, npd_P10, npd_P01] at h10 h01
    have e0 : f 0 + 1 = 0 := by have := congrFun h10 0; simpa using this
    have e1 : f 1 = 0 := by have := congrFun h10 1; simpa using this
    have := congrFun h01 0
    simp only [Matrix.cons_val_zero] at this
    omega





theorem jsf_starHull_unitCell_eq : ndt_StarHull unitCell = unitCell :=
  Set.Subset.antisymm
    (ndt_starHull_subset_of_fillClosed (le_refl _) jsf_unitCell_fillClosed)
    (ndt_subset_starHull _)











theorem jsf_starHull_unitCell_bdEdgeMatch :
    pww_BdEdgeMatch (ndt_StarHull unitCell) (mpl_orbitLoop unitCell ucBase) := by
  rw [jsf_starHull_unitCell_eq]; exact jsf_unitCell_bdEdgeMatch




















theorem jsf_starHull_bdEdgeMatch_of_rayParity (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hin : ∀ z, z ∈ ndt_StarHull K →
      ¬ Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a)))
    (hout : ∀ z, z ∉ ndt_StarHull K →
      Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a))) :
    pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) a) :=
  jsf_bdEdgeMatch_of_rayParity (mpl_orbitLoop (ndt_StarHull K) a) hin hout

























































end Lattice

end StatMech
