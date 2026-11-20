/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.FloodFillConnected
import Code.Lattice.OutsideConnected

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}








theorem kc4_notMem_supportSet_iff (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    z ∉ oc_supportSet Vc ↔ z ∉ Vc.support := by
  rw [oc_mem_supportSet]

















theorem kc4_offSupportWalk_of_reachable (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∉ Vc.support)
    (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
  obtain ⟨w⟩ := h
  obtain ⟨p, hp, _⟩ := ffc_project_walk w ((kc4_notMem_supportSet_iff Vc x).mpr hx)
  refine ⟨p, fun z hz => (kc4_notMem_supportSet_iff Vc z).mp (hp z hz)⟩








theorem kc4_reachable_of_offSupportWalk (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y :=
  ⟨ffc_lift_walk p (fun z hz => (kc4_notMem_supportSet_iff Vc z).mpr (hp z hz))⟩














theorem kc4_reachable_iff_offSupportWalk (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∉ Vc.support) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y ↔
      ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support :=
  ⟨kc4_offSupportWalk_of_reachable Vc hx, fun ⟨p, hp⟩ => kc4_reachable_of_offSupportWalk Vc p hp⟩











theorem kc4_offSupportWalk_endpoint_offSupport (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    x ∉ Vc.support ∧ y ∉ Vc.support :=
  ⟨hp x p.start_mem_support, hp y p.end_mem_support⟩






theorem kc4_reachable_offSupport_symm (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∉ Vc.support) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y ↔
      y ∉ Vc.support ∧ ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
  rw [kc4_reachable_iff_offSupportWalk Vc hx]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨(kc4_offSupportWalk_endpoint_offSupport Vc p hp).2, p, hp⟩
  · rintro ⟨_, p, hp⟩
    exact ⟨p, hp⟩












theorem kc4_no_offSupportWalk_of_mem_support (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (hx : x ∈ Vc.support) :
    ¬ ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
  rintro ⟨p, hp⟩
  exact hp x p.start_mem_support hx





theorem kc4_offSupportWalk_iff_sharp (Vc : (hypercubicLattice 2).Walk a a) {x : Site 2}
    (hx : x ∈ Vc.support) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x x ∧
      ¬ ∃ p : (hypercubicLattice 2).Walk x x, ∀ z ∈ p.support, z ∉ Vc.support :=
  ⟨SimpleGraph.Reachable.refl _, kc4_no_offSupportWalk_of_mem_support Vc hx⟩














theorem kc4_node_nonvacuous :
    let Vc : (hypercubicLattice 2).Walk (![5, 5] : Site 2) ![5, 5] := SimpleGraph.Walk.nil
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable (![0, 0] : Site 2) ![1, 0] ∧
      ∃ p : (hypercubicLattice 2).Walk (![0, 0] : Site 2) ![1, 0],
        ∀ z ∈ p.support, z ∉ Vc.support := by
  intro Vc
  have hsuppVc : Vc.support = [(![5, 5] : Site 2)] := SimpleGraph.Walk.support_nil
  have hseed : (![0, 0] : Site 2) ∉ Vc.support := by
    rw [hsuppVc]; simp only [List.mem_singleton]
    intro h; have := congrFun h 0; simp at this
  have htgt : (![1, 0] : Site 2) ∉ Vc.support := by
    rw [hsuppVc]; simp only [List.mem_singleton]
    intro h; have := congrFun h 0; simp at this
  have hadj : (hypercubicLattice 2).Adj (![0, 0] : Site 2) ![1, 0] := by
    rw [hypercubicLattice_adj]; decide
  
  
  
  have hwalk_off : ∀ z ∈ (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).support,
      z ∉ Vc.support := by
    intro z hz
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hz
    rcases hz with h | h
    · exact h ▸ hseed
    · exact h ▸ htgt
  refine ⟨?_, ?_⟩
  · exact kc4_reachable_of_offSupportWalk Vc (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
      hwalk_off
  · exact kc4_offSupportWalk_of_reachable Vc hseed
      (kc4_reachable_of_offSupportWalk Vc (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
        hwalk_off)

end Walls

end StatMech
