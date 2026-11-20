/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.TurningNumber
import Code.Lattice.ContourLinksExits
import Code.Lattice.EarExistence
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitEncloses
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Walls.jc10farupeven
import Code.Walls.jc10localconstancy
import Code.Walls.jc10cornerexists
import Code.Walls.jc10cornercellinK

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice









theorem jc10core_countP_or_decomp {α : Type*} (l : List α) (p q r : α → Prop) [DecidablePred p]
    [DecidablePred q] [DecidablePred r]
    (hdec : ∀ a, p a ↔ (q a ∨ r a)) (hexcl : ∀ a, ¬ (q a ∧ r a)) :
    l.countP (fun a => decide (p a)) =
      l.countP (fun a => decide (q a)) + l.countP (fun a => decide (r a)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, ih]
    by_cases hq : q a <;> by_cases hr : r a
    · exact absurd ⟨hq, hr⟩ (hexcl a)
    · have hp : p a := (hdec a).mpr (Or.inl hq)
      simp only [hp, hq, hr, decide_false, if_false, Bool.false_eq_true, decide_true]
      omega
    · have hp : p a := (hdec a).mpr (Or.inr hr)
      simp only [hp, hq, hr, decide_false, if_false, Bool.false_eq_true, decide_true]
      omega
    · have hp : ¬ p a := fun h => by rcases (hdec a).mp h with h' | h' <;> [exact hq h'; exact hr h']
      simp only [hp, hq, hr, decide_false, if_false, Bool.false_eq_true]
      omega










theorem jc10core_dartFace_row_le_tail (e : Dart) : (dartFace e) 1 ≤ e.tail 1 := by
  unfold dartFace
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h1 : Lattice.negPart (e.dir 1) ≤ 0 := by unfold Lattice.negPart; split_ifs <;> omega
  have h2 : Lattice.negPart (rot90Fun e.dir 1) ≤ 0 := by unfold Lattice.negPart; split_ifs <;> omega
  omega






theorem jc10core_support_row_le (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) (p : Site 2)
    (hp : p ∈ (mpl_orbitLoop K a).support) : p 1 ≤ c 1 := by
  rw [mpl_orbitLoop_support, mpl_orbitFaceLoop, SimpleGraph.Walk.support_copy,
    dartOrbitFaceWalk_support, List.mem_map] at hp
  obtain ⟨k, _, hk⟩ := hp
  subst hk
  have htail : ((dartNext K)^[k] a.1).tail ∈ K :=
    (iterate_isBoundaryDart K a.1 a.2 k).tail_mem
  have hrow : (dartFace ((dartNext K)^[k] a.1)) 1 ≤ ((dartNext K)^[k] a.1).tail 1 :=
    jc10core_dartFace_row_le_tail _
  by_contra hcon
  push Not at hcon
  exact extremeCell_not_mem_of_higher K c _ hc (by omega) htail




theorem jc10core_colPt_off_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) (j : ℤ) (hj : c 1 < j) :
    (![c 0, j] : Site 2) ∉ (mpl_orbitLoop K a).support := by
  intro hmem
  have := jc10core_support_row_le K a c hc _ hmem
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  omega












theorem jc10core_col_parity_const (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) (n : ℕ) :
    (Even (jec_rayCount (![c 0, c 1 + 1 + (n : ℤ)] : Site 2) (mpl_orbitLoop K a)) ↔
      Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hadj : (hypercubicLattice 2).Adj (![c 0, c 1 + 1 + (m : ℤ)] : Site 2)
        (![c 0, c 1 + 1 + (m : ℤ) + 1] : Site 2) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      norm_num
    have hu : (![c 0, c 1 + 1 + (m : ℤ)] : Site 2) ∉ (mpl_orbitLoop K a).support :=
      jc10core_colPt_off_support K a c hc _ (by omega)
    have hv : (![c 0, c 1 + 1 + (m : ℤ) + 1] : Site 2) ∉ (mpl_orbitLoop K a).support :=
      jc10core_colPt_off_support K a c hc _ (by omega)
    have hstep := jc10_localConstancy (mpl_orbitLoop K a) hadj hu hv
    have hcast : c 1 + 1 + ((m : ℤ) + 1) = c 1 + 1 + (m : ℤ) + 1 := by ring
    rw [Nat.cast_succ, hcast, ← hstep]; exact ih





theorem jc10core_above_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) :
    Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)) := by
  
  obtain ⟨R, hR⟩ := jc10_orbitLoop_box_confined K a
  
  set N : ℕ := ((R : ℤ) + 1 - c 1).toNat + 1 with hN
  have hbig : (R : ℤ) < c 1 + 1 + (N : ℤ) := by
    have h2 : ((R : ℤ) + 1 - c 1) ≤ ((R : ℤ) + 1 - c 1).toNat := Int.self_le_toNat _
    push_cast [hN]
    omega
  
  have hfar : Even (jec_rayCount (![c 0, c 1 + 1 + (N : ℤ)] : Site 2) (mpl_orbitLoop K a)) := by
    refine jc10_farUp_even (mpl_orbitLoop K a) R hR (![c 0, c 1 + 1 + (N : ℤ)] : Site 2) ?_
    simpa using hbig
  exact (jc10core_col_parity_const K a c hc N).mp hfar













def jc10core_topWallEdge (c : Site 2) (e : Sym2 (Site 2)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y =>
      (x 1 = y 1 ∧ x 1 = c 1) ∧
      ((x 0 = c 0 - 1 ∧ y 0 = c 0) ∨ (y 0 = c 0 - 1 ∧ x 0 = c 0)), by
    intro x y; simp only [eq_iff_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.symm, h1 ▸ h2⟩, by tauto⟩⟩ e

@[simp] theorem jc10core_topWallEdge_mk (c x y : Site 2) :
    jc10core_topWallEdge c s(x, y) ↔
      (x 1 = y 1 ∧ x 1 = c 1) ∧
      ((x 0 = c 0 - 1 ∧ y 0 = c 0) ∨ (y 0 = c 0 - 1 ∧ x 0 = c 0)) := by
  unfold jc10core_topWallEdge; rfl

open Classical in


noncomputable def jc10core_topWallCount (c : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (jc10core_topWallEdge c e))




theorem jc10core_wallEdge_up_decomp (c x y : Site 2) :
    jec_wallEdge (![c 0, c 1 + 1] : Site 2) s(x, y) ↔
      (jec_wallEdge c s(x, y) ∨ jc10core_topWallEdge c s(x, y)) := by
  rw [jec_wallEdge_mk, jec_wallEdge_mk, jc10core_topWallEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega



theorem jc10core_wallEdge_topWall_excl (c x y : Site 2) :
    ¬ (jec_wallEdge c s(x, y) ∧ jc10core_topWallEdge c s(x, y)) := by
  rw [jec_wallEdge_mk, jc10core_topWallEdge_mk]; omega









theorem jc10core_wallCount_up (c : Site 2) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    jec_wallCount (![c 0, c 1 + 1] : Site 2) w =
      jec_wallCount c w + jc10core_topWallCount c w := by
  classical
  rw [jec_wallCount, jec_wallCount, jc10core_topWallCount]
  exact jc10core_countP_or_decomp w.edges
    (fun e => jec_wallEdge (![c 0, c 1 + 1] : Site 2) e)
    (fun e => jec_wallEdge c e) (fun e => jc10core_topWallEdge c e)
    (fun e => by induction e using Sym2.ind with | _ x y => exact jc10core_wallEdge_up_decomp c x y)
    (fun e => by induction e using Sym2.ind with | _ x y => exact jc10core_wallEdge_topWall_excl c x y)























theorem jc10core_cornerCellOdd_of_topWallOdd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hc : IsExtremeCell K c)
    (htop : ¬ Even (jc10core_topWallCount c (mpl_orbitLoop K a))) :
    ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) := by
  
  have haboveR : Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)) :=
    jc10core_above_even K a c hc
  have haboveW : Even (jec_wallCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)) :=
    (jec_loop_ray_wall_parity (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)).mp haboveR
  
  have hsplit := jc10core_wallCount_up c (mpl_orbitLoop K a)
  
  rw [hsplit, Nat.even_add] at haboveW
  have hwallOdd : ¬ Even (jec_wallCount c (mpl_orbitLoop K a)) := fun hwe => htop (haboveW.mp hwe)
  
  rw [jec_loop_ray_wall_parity c (mpl_orbitLoop K a)]
  exact hwallOdd




theorem jc10core_windingWitness_of_topWallOdd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hc : IsExtremeCell K c)
    (htop : ¬ Even (jc10core_topWallCount c (mpl_orbitLoop K a))) :
    ∃ z₀ : Site 2, z₀ ∈ K ∧ ¬ Even (jec_rayCount z₀ (mpl_orbitLoop K a)) :=
  ⟨c, hc.mem, jc10core_cornerCellOdd_of_topWallOdd K a c hc htop⟩

















def jc10core_TopWallOdd (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) :
    Prop :=
  ¬ Even (jc10core_topWallCount c (mpl_orbitLoop K a))



theorem jc10core_cornerCellOdd_of_residue (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hc : IsExtremeCell K c)
    (hres : jc10core_TopWallOdd K a c) :
    ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) :=
  jc10core_cornerCellOdd_of_topWallOdd K a c hc hres





theorem jc10core_exists_windingWitness_of_residue (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty)
    (hres : ∀ c : Site 2, ∀ hc : IsExtremeCell K c,
      jc10core_TopWallOdd K (extremeBase K c hc) c) :
    ∃ c : Site 2, ∀ hc : IsExtremeCell K c,
      c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, fun hc' => ⟨hc'.mem,
    jc10core_cornerCellOdd_of_residue K (extremeBase K c hc') c hc' (hres c hc')⟩⟩












theorem jc10core_unitCell_topWallCount_eq_one :
    jc10core_topWallCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase) = 1 := by
  classical
  rw [jc10core_topWallCount, mpl_orbitLoop_edges, mpl_unitCell_faceLoop_edges]
  simp only [List.countP_cons, List.countP_nil]
  have h1 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![0, 0] : Site 2), ![0, -1])) =
      false := by
    simp only [decide_eq_false_iff_not, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have h2 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![0, -1] : Site 2), ![-1, -1])) =
      false := by
    simp only [decide_eq_false_iff_not, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have h3 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![-1, -1] : Site 2), ![-1, 0])) =
      false := by
    simp only [decide_eq_false_iff_not, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have h4 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![-1, 0] : Site 2), ![0, 0])) =
      true := by
    simp only [decide_eq_true_eq, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  rw [h1, h2, h3, h4]
  decide




theorem jc10core_unitCell_topWall_odd :
    jc10core_TopWallOdd unitCell ucBase (![0, 0] : Site 2) := by
  unfold jc10core_TopWallOdd
  rw [jc10core_unitCell_topWallCount_eq_one]
  decide





theorem jc10core_unitCell_cornerCellOdd :
    ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
  rw [mpl_unitCell_rayCount_eq_one]; decide




































end Walls

end StatMech
