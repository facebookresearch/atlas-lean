/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.JordanZ2
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanCycleSpace
import Code.Lattice.JordanContour
import Code.Lattice.ClosedContourSeparation

open Set SimpleGraph Function

namespace StatMech

namespace Lattice










theorem jsc_walk_col_bound {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a b) :
    ∃ M : ℤ, ∀ p ∈ Vc.support, p 0 ≤ M := by
  classical
  refine ⟨(Vc.support.map (fun p => p 0)).foldr max 0, ?_⟩
  intro p hp
  have hmem : p 0 ∈ Vc.support.map (fun p => p 0) := List.mem_map_of_mem hp
  
  have hkey : ∀ (l : List ℤ) (x : ℤ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; exact absurd hx (List.not_mem_nil)
    | cons c t ih =>
      intro x hx
      rw [List.foldr_cons]
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih x hx) (le_max_right _ _)
  exact hkey _ _ hmem












theorem jsc_exists_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∃ q : Site 2, q ∉ jec_leftRegion Vc ∧ ∀ p ∈ Vc.support, p 0 ≤ q 0 - 1 := by
  obtain ⟨M, hM⟩ := jsc_walk_col_bound Vc
  refine ⟨![M + 1, 0], ?_, ?_⟩
  · rw [jec_mem_leftRegion, not_not]
    refine jec_ray_even_far Vc ![M + 1, 0] ?_
    intro p hp
    have := hM p hp
    simp only [Matrix.cons_val_zero]; omega
  · intro p hp
    have := hM p hp
    simp only [Matrix.cons_val_zero]; omega






theorem jsc_inside_not_reachable_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : ¬ Even (jec_rayCount x Vc)) (hy : Even (jec_rayCount y Vc)) :
    ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  not_reachable_latticeMinusBarrier (jec_leftRegion Vc)
    (by rw [jec_mem_leftRegion]; exact hx)
    (by rw [jec_mem_leftRegion, not_not]; exact hy)





theorem jsc_side_constant {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (h : (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) :
    (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
  have hb := barrier_sameSide_of_reachable (jec_leftRegion Vc) h
  simp only [jec_mem_leftRegion] at hb
  exact not_iff_not.mp hb


















theorem jsc_two_components_of_connected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨q, _hq, hqfar⟩ := jsc_exists_outside Vc
  exact ccs_closedLoop_two_components Vc hp hqfar hin hout














def jsc_JordanSeparates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∃ p, ¬ Even (jec_rayCount p Vc)) ∧
    (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) ∧
    (∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)










theorem jsc_separation_of_JordanSeparates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : jsc_JordanSeparates Vc) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 ∧
      (∃ q : Site 2, q ∉ jec_leftRegion Vc) ∧
      (∀ x y : Site 2, ¬ Even (jec_rayCount x Vc) → Even (jec_rayCount y Vc) →
        ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) := by
  obtain ⟨⟨p, hp⟩, hin, hout⟩ := h
  obtain ⟨q, hq, _⟩ := jsc_exists_outside Vc
  exact ⟨jsc_two_components_of_connected Vc hp hin hout, ⟨q, hq⟩,
    fun x y hx hy => jsc_inside_not_reachable_outside Vc hx hy⟩














theorem jsc_cycle_faceCount_eq_two {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 :=
  jcs_cycle_faceCount_eq_two c hc











theorem jsc_cycle_separation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (hsep : jsc_JordanSeparates Vc) :
    faceCount Vc.toSubgraph.coe = 2 ∧
      Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨⟨p, hp⟩, hin, hout⟩ := hsep
  exact ⟨jsc_cycle_faceCount_eq_two Vc hcyc, jsc_two_components_of_connected Vc hp hin hout⟩















theorem jsc_cluster_inside_connected (o : Site 2) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hy : y ∈ cluster 2 ω o) :
    (latticeMinusBarrier (cluster 2 ω o)).Reachable x y :=
  cluster_reachable_in_barrier o hx hy















theorem jsc_separation_of_loopBridge (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    (hloop : ccs_OrbitIsLoop (cluster 2 ω o))
    (hout : ∀ s t : Site 2, s ∉ cluster 2 ω o → t ∉ cluster 2 ω o →
        (latticeMinusBarrier (cluster 2 ω o)).Reachable s t) :
    Nat.card (latticeMinusBarrier (cluster 2 ω o)).ConnectedComponent = 2 ∧
      ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
        cluster 2 ω o = jec_leftRegion Vc := by
  obtain ⟨R, hR⟩ := finite_subset_box (cluster 2 ω o) hfin
  
  have hpin : o ∈ cluster 2 ω o := self_mem_cluster ω o
  
  have hbe : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hqout : beacon 2 R ∉ cluster 2 ω o := (exterior_subset_compl (cluster 2 ω o) R hR) hbe
  refine ccs_cluster_two_components (K := cluster 2 ω o) hloop hpin hqout ?_ hout
  
  intro s t hs ht; exact cluster_reachable_in_barrier o hs ht












noncomputable def jsc_unitSquareLoop : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] :=
  let s1 : (hypercubicLattice 2).Walk ![0, 0] ![0, 1] :=
    (jec_vsegUp 0 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![0, 1] ![1, 1] :=
    (jec_hsegRight 1 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![1, 1] ![1, 0] :=
    ((jec_vsegUp 1 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![1, 0] ![0, 0] :=
    ((jec_hsegRight 0 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append s4))





theorem jsc_unitSquareLoop_inside_odd :
    ¬ Even (jec_rayCount (![1, 1] : Site 2) jsc_unitSquareLoop) := by
  have hcount : jec_rayCount (![1, 1] : Site 2) jsc_unitSquareLoop = 1 := by
    unfold jsc_unitSquareLoop
    simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
      jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    norm_num
  rw [hcount]; decide







theorem jsc_JordanSeparates_inside_satisfiable :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), ∃ p, ¬ Even (jec_rayCount p Vc) :=
  ⟨_, jsc_unitSquareLoop, _, jsc_unitSquareLoop_inside_odd⟩

end Lattice

end StatMech
