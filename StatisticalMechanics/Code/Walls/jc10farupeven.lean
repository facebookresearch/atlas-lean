/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice












theorem jc10_rayCount_eq_zero_of_above (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, p 1 ≤ z 1 - 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he
  obtain ⟨u, v⟩ := e
  have hu := h u (w.fst_mem_support_of_mem_edges he)
  have hv := h v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]
  change ¬ jec_rayEdge z s(u, v)
  rw [jec_rayEdge_mk]
  
  omega




theorem jc10_even_of_above (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, p 1 ≤ z 1 - 1) :
    Even (jec_rayCount z w) := by
  rw [jc10_rayCount_eq_zero_of_above z w h]
  exact Nat.even_iff.mpr rfl











theorem jc10_support_row_bound {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) (R : ℕ)
    (hsupp : ∀ p ∈ w.support, p ∈ box 2 R) {p : Site 2} (hp : p ∈ w.support) :
    -(R : ℤ) ≤ p 1 ∧ p 1 ≤ (R : ℤ) := by
  have hnat : (p 1).natAbs ≤ R := mem_box.mp (hsupp p hp) 1
  have habs : |p 1| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hnat
  rw [abs_le] at habs
  exact habs






theorem jc10_rayCount_eq_zero_of_box {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (R : ℕ)
    (hsupp : ∀ p ∈ w.support, p ∈ box 2 R) (z : Site 2) (hz : (R : ℤ) < z 1) :
    jec_rayCount z w = 0 := by
  refine jc10_rayCount_eq_zero_of_above z w ?_
  intro p hp
  have hbound := jc10_support_row_bound w R hsupp hp
  omega






theorem jc10_farUp_even {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (R : ℕ)
    (hsupp : ∀ p ∈ w.support, p ∈ box 2 R) (z : Site 2) (hz : (R : ℤ) < z 1) :
    Even (jec_rayCount z w) := by
  rw [jc10_rayCount_eq_zero_of_box w R hsupp z hz]
  exact Nat.even_iff.mpr rfl










theorem jc10_orbitLoop_box_confined (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ∃ R : ℕ, ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R := by
  obtain ⟨R, hR⟩ := finite_subset_box {p : Site 2 | p ∈ (mpl_orbitLoop K a).support}
    (List.finite_toSet _)
  exact ⟨R, fun p hp => hR hp⟩






theorem jc10_orbitLoop_rayCount_eq_zero_of_above (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, p 1 ≤ z 1 - 1) :
    jec_rayCount z (mpl_orbitLoop K a) = 0 :=
  jc10_rayCount_eq_zero_of_above z (mpl_orbitLoop K a) hfar




theorem jc10_orbitLoop_farUp_even (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, p 1 ≤ z 1 - 1) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  jc10_even_of_above z (mpl_orbitLoop K a) hfar





theorem jc10_orbitLoop_farUp_even_of_box (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R) (z : Site 2) (hz : (R : ℤ) < z 1) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  jc10_farUp_even (mpl_orbitLoop K a) R hsupp z hz














theorem jc10_unitCell_farUp_rayCount :
    jec_rayCount (![0, 5] : Site 2) (mpl_orbitLoop unitCell ucBase) = 0 := by
  classical
  rw [jec_rayCount, mpl_orbitLoop_edges, mpl_unitCell_faceLoop_edges]
  simp only [List.countP_cons, List.countP_nil]
  have h1 : decide (jec_rayEdge (![0, 5] : Site 2) s((![0, 0] : Site 2), ![0, -1])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h2 : decide (jec_rayEdge (![0, 5] : Site 2) s((![0, -1] : Site 2), ![-1, -1])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h3 : decide (jec_rayEdge (![0, 5] : Site 2) s((![-1, -1] : Site 2), ![-1, 0])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h4 : decide (jec_rayEdge (![0, 5] : Site 2) s((![-1, 0] : Site 2), ![0, 0])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [h1, h2, h3, h4]
  norm_num






theorem jc10_unitCell_farUp_even :
    Even (jec_rayCount (![0, 5] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
  rw [jc10_unitCell_farUp_rayCount]
  exact Nat.even_iff.mpr rfl

end Walls

end StatMech
