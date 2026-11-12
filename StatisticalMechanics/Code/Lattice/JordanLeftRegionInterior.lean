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
import Code.Lattice.JordanCycleSpace
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.MinimalPeriodLoop

open Set SimpleGraph Function

namespace StatMech

namespace Lattice
















theorem jlri_sameRegion_along_offSupport_walk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
  have hpar := oee_rayParity_const_along_walk Vc p hp
  
  simp only [jec_mem_leftRegion]
  exact not_congr hpar












theorem jlri_leftRegion_bdEdge_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd





theorem jlri_no_bdEdge_off_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    ¬ bdEdge (jec_leftRegion Vc) s(u, v) := by
  
  have hsame : (u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc) :=
    jlri_sameRegion_along_offSupport_walk Vc (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
      (by
        intro z hz
        rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hz
        rcases List.mem_cons.mp hz with h | h
        · exact h ▸ hu
        · rcases List.mem_singleton.mp h with h'; exact h' ▸ hv)
  rw [bdEdge_mk]
  tauto







theorem jlri_bdEdge_iff_endpoint_on_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) →
      (u ∈ Vc.support ∨ v ∈ Vc.support) := by
  intro hbd
  exact jlri_leftRegion_bdEdge_support Vc hadj hbd














theorem jlri_offSupport_adj_in_barrier {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Adj u v :=
  ⟨hadj, jlri_no_bdEdge_off_support Vc hadj hu hv⟩





theorem jlri_offSupport_walk_in_barrier {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w c hadj q ih =>
    have hu : u ∉ Vc.support := hp u (by simp)
    have hw : w ∉ Vc.support := hp w (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := by
      intro z hz
      exact hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    exact (jlri_offSupport_adj_in_barrier Vc hadj hu hw).reachable.trans (ih htail)











theorem jlri_inside_reachable_of_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t := by
  intro s t hs ht
  obtain ⟨p, hp⟩ := hInOff s t hs ht
  exact jlri_offSupport_walk_in_barrier Vc p hp




theorem jlri_outside_reachable_of_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
      (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t := by
  intro s t hs ht
  obtain ⟨p, hp⟩ := hOutOff s t hs ht
  exact jlri_offSupport_walk_in_barrier Vc p hp



















theorem jlri_two_components_of_offSupport_connected {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  ccs_closedLoop_two_components Vc hp hq
    (jlri_inside_reachable_of_offSupport Vc hInOff)
    (jlri_outside_reachable_of_offSupport Vc hOutOff)












theorem jlri_minimalLoop_sameRegion (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support) :
    (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) :=
  jlri_sameRegion_along_offSupport_walk (mpl_orbitLoop K a) p hp




theorem jlri_minimalLoop_no_bdEdge_off_support (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    ¬ bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v) :=
  jlri_no_bdEdge_off_support (mpl_orbitLoop K a) hadj hu hv


theorem jlri_minimalLoop_offSupport_walk_in_barrier (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support) :
    (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).Reachable x y :=
  jlri_offSupport_walk_in_barrier (mpl_orbitLoop K a) p hp






theorem jlri_minimalLoop_two_components (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
    (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
        t ∈ jec_leftRegion (mpl_orbitLoop K a) →
        ∃ pw : (hypercubicLattice 2).Walk s t,
          ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support)
    (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion (mpl_orbitLoop K a) →
        t ∉ jec_leftRegion (mpl_orbitLoop K a) →
        ∃ pw : (hypercubicLattice 2).Walk s t,
          ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support) :
    Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 :=
  jlri_two_components_of_offSupport_connected (mpl_orbitLoop K a) hp hq hInOff hOutOff

end Lattice

end StatMech
