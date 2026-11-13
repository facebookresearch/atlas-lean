/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanContour
import Code.Lattice.JordanCycleSpace
import Code.Lattice.PlanarFaceGeometric
import Code.Lattice.PlanarTopology
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.EulerGeneral

open Set SimpleGraph Function

namespace StatMech

namespace Lattice















theorem egf_loop_barrier_on_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbar : ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Adj u v) :
    u ∈ Vc.support ∨ v ∈ Vc.support := by
  rw [latticeMinusBarrier_adj] at hbar
  push Not at hbar
  exact jec_leftRegion_bdEdge_support Vc hadj (hbar hadj)





theorem egf_leftRegion_sameSide {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (h : (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) :
    (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) :=
  barrier_sameSide_of_reachable (jec_leftRegion Vc) h










theorem egf_rayCount_zero_above (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (R : ℤ)
    (hsupp : ∀ p ∈ w.support, p 1 ≤ R) (hz : R + 1 ≤ z 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he
  obtain ⟨u, v⟩ := e
  have hu := hsupp u (w.fst_mem_support_of_mem_edges he)
  have hv := hsupp v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]; show ¬ jec_rayEdge z s(u, v); rw [jec_rayEdge_mk]; omega


theorem egf_rayCount_zero_below (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (R : ℤ)
    (hsupp : ∀ p ∈ w.support, -R ≤ p 1) (hz : z 1 ≤ -R) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he
  obtain ⟨u, v⟩ := e
  have hu := hsupp u (w.fst_mem_support_of_mem_edges he)
  have hv := hsupp v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]; show ¬ jec_rayEdge z s(u, v); rw [jec_rayEdge_mk]; omega











theorem egf_ray_even_exterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2}
    (hz : z ∈ exterior 2 R) :
    Even (jec_rayCount z Vc) := by
  have hsx : ∀ p ∈ Vc.support, -(R:ℤ) ≤ p 0 ∧ p 0 ≤ R := by
    intro p hp; have := hsupp p hp; rw [mem_box] at this; have h0 := this 0; omega
  have hsy : ∀ p ∈ Vc.support, -(R:ℤ) ≤ p 1 ∧ p 1 ≤ R := by
    intro p hp; have := hsupp p hp; rw [mem_box] at this; have h1 := this 1; omega
  rw [mem_exterior] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i
  · 
    have hi0 : (R:ℕ) < (z 0).natAbs := hi
    rcases le_or_gt 0 (z 0) with hsgn | hsgn
    · 
      have hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1 := by
        intro p hp; have h2 := (hsx p hp).2; omega
      exact jec_ray_even_far Vc z hfar
    · 
      have hzero : jec_rayCount z Vc = 0 := by
        refine jec_rayCount_eq_zero_of_right z Vc ?_
        intro p hp; have h1 := (hsx p hp).1; omega
      rw [hzero]; exact ⟨0, rfl⟩
  · 
    have hi1 : (R:ℕ) < (z 1).natAbs := hi
    rcases le_or_gt 0 (z 1) with hsgn | hsgn
    · 
      have hzero : jec_rayCount z Vc = 0 :=
        egf_rayCount_zero_above z Vc R (fun p hp => (hsy p hp).2) (by omega)
      rw [hzero]; exact ⟨0, rfl⟩
    · 
      have hzero : jec_rayCount z Vc = 0 :=
        egf_rayCount_zero_below z Vc R (fun p hp => (hsy p hp).1) (by omega)
      rw [hzero]; exact ⟨0, rfl⟩




theorem egf_exterior_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2}
    (hz : z ∈ exterior 2 R) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion]; push Not; exact egf_ray_even_exterior Vc R hsupp hz




theorem egf_leftRegion_subset_box {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    jec_leftRegion Vc ⊆ box 2 R := by
  intro z hz
  by_contra hzbox
  have hzext : z ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hzbox
  exact egf_exterior_outside Vc R hsupp hzext hz


theorem egf_leftRegion_finite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc).Finite :=
  (box_finite 2 R).subset (egf_leftRegion_subset_box Vc R hsupp)











theorem egf_exterior_reachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
  have hsub : exterior 2 R ⊆ (jec_leftRegion Vc)ᶜ :=
    fun z hz => egf_exterior_outside Vc R hsupp hz
  have hmap := (box_exterior_connected R (by norm_num) x y hx hy).map
    (extToBarrierHom (jec_leftRegion Vc) R hsub)
  simpa [extToBarrierHom] using hmap




theorem egf_outsideComponent_infinite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    ((latticeMinusBarrier (jec_leftRegion Vc)).connectedComponentMk (beacon 2 R)).supp.Infinite := by
  have hsub : jec_leftRegion Vc ⊆ box 2 R := egf_leftRegion_subset_box Vc R hsupp
  exact outsideComponent_infinite (jec_leftRegion Vc) R hsub















def egf_LoopFloodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∃ x, x ∈ jec_leftRegion Vc) ∧ (∃ y, y ∉ jec_leftRegion Vc) ∧
    (∀ p q : Site 2, p ∈ jec_leftRegion Vc → q ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable p q) ∧
    (∀ p q : Site 2, p ∉ jec_leftRegion Vc → q ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable p q)






theorem egf_loop_two_components {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : egf_LoopFloodFill Vc) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hin, hout⟩ := h
  exact jcs_two_components_of_sides (jec_leftRegion Vc) hx hy hin hout












theorem egf_cycle_faceCount_eq_two {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 :=
  jcs_cycle_faceCount_eq_two c hc







theorem egf_cycle_two_components {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle)
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (h : egf_LoopFloodFill Vc) :
    faceCount c.toSubgraph.coe = 2 ∧
      Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  ⟨egf_cycle_faceCount_eq_two c hc, egf_loop_two_components Vc h⟩






























theorem egf_face_eq_geometric (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    faceCount P.G = geometricRegionCount P + 1 :=
  faceCount_eq_geometric_regions P hJ






theorem egf_geometricRegionCount_eq_nullity (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    geometricRegionCount P = nullity P.G :=
  geometricRegionCount_eq_nullity P hJ






theorem egf_euler_geometric (P : PlanarZ2Subgraph) (hJ : DiscreteJordanSeparation P) :
    (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1)
      = 1 + Nat.card P.G.ConnectedComponent :=
  euler_geometric_regions P hJ









































end Lattice

end StatMech
