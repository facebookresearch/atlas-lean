/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Lattice.PeierlsHoleFreeBoundary
import Code.Lattice.BdEdgeMatchClose
import Code.Walls.rpccrossflip
import Code.Walls.dowdartwinding

















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.Walls



theorem rlc_crossEdge_eq_flankFaces {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v) :
    rpc_crossEdge u v = flankFaces u v := by
  classical
  rcases adj_cases hadj with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
  · simp [rpc_crossEdge, flankFaces, rpc_vCrossEdge, h0, h1]
    omega
  · simp [rpc_crossEdge, flankFaces, rpc_vCrossEdge, h0, h1]
  · simp [rpc_crossEdge, flankFaces, rpc_hCrossEdge, h0, h1]
    omega
  · simp [rpc_crossEdge, flankFaces, rpc_hCrossEdge, h0, h1]



theorem rlc_adjacent_bdEdge_match_of_faceBoundaryTrail
    (K : Set (Site 2)) {f : Site 2}
    (c : (faceBoundaryGraph K).Walk f f)
    (htrail : c.IsTrail)
    (hcover : ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge K s(u, v) ↔
      bdEdge (jec_leftRegion
        (c.mapLe (faceBoundaryGraph_le K))) s(u, v) := by
  let C := c.mapLe (faceBoundaryGraph_le K)
  have hnd : C.edges.Nodup := by
    simpa [C, SimpleGraph.Walk.edges_mapLe_eq_edges] using htrail.edges_nodup
  have hmem : rpc_crossEdge u v ∈ C.edges ↔
      rpc_crossEdge u v ∈ (faceBoundaryGraph K).edgeSet := by
    rw [show C.edges = c.edges by
      simp [C, SimpleGraph.Walk.edges_mapLe_eq_edges]]
    constructor
    · intro he
      exact c.edges_subset_edgeSet he
    · exact hcover _
  rw [rpc_crossFlip C hadj,
    dow_walk_odd_count_iff_mem C hnd (rpc_crossEdge u v), hmem,
    rlc_crossEdge_eq_flankFaces hadj,
    phb_flankFaces_mem_faceBoundaryGraph_iff hadj]

private theorem rlc_agreement_const_along_lattice_walk
    (S T : Set (Site 2))
    (hbd : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (bdEdge S s(u, v) ↔ bdEdge T s(u, v)))
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    ((x ∈ S ↔ x ∈ T) ↔ (y ∈ S ↔ y ∈ T)) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons u v z huv w ih =>
      have h := hbd huv
      rw [bdEdge_mk, bdEdge_mk] at h
      have hstep : ((u ∈ S ↔ u ∈ T) ↔ (v ∈ S ↔ v ∈ T)) := by
        tauto
      exact hstep.trans ih



theorem rlc_setIdentity_of_adjacent_bdEdge_match
    (S T : Set (Site 2))
    (hbd : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (bdEdge S s(u, v) ↔ bdEdge T s(u, v))) :
    S = T ∨ S = Tᶜ := by
  classical
  have hagree (x y : Site 2) :
      ((x ∈ S ↔ x ∈ T) ↔ (y ∈ S ↔ y ∈ T)) := by
    obtain ⟨w⟩ := pbs_reach_all x y
    exact rlc_agreement_const_along_lattice_walk S T hbd w
  by_cases h0 : ((default : Site 2) ∈ S ↔ (default : Site 2) ∈ T)
  · left
    ext x
    exact (hagree default x).mp h0
  · right
    ext x
    simp only [Set.mem_compl_iff]
    have hx : ¬ (x ∈ S ↔ x ∈ T) := fun hx =>
      h0 ((hagree default x).mpr hx)
    tauto



theorem rlc_leftRegion_eq_of_faceBoundaryTrail
    (K : Set (Site 2)) (hK : K.Finite) {f : Site 2}
    (c : (faceBoundaryGraph K).Walk f f)
    (htrail : c.IsTrail)
    (hcover : ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges) :
    K = jec_leftRegion (c.mapLe (faceBoundaryGraph_le K)) := by
  let C := c.mapLe (faceBoundaryGraph_le K)
  have hid : K = jec_leftRegion C ∨ K = (jec_leftRegion C)ᶜ :=
    rlc_setIdentity_of_adjacent_bdEdge_match K (jec_leftRegion C) (by
      intro u v hadj
      exact rlc_adjacent_bdEdge_match_of_faceBoundaryTrail
        K c htrail hcover hadj)
  have hsupport : ({z | z ∈ C.support} : Set (Site 2)).Finite := by
    simp
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box _ hsupport
  exact bemc_orientation_selected C R hR hK hid



theorem rlc_exists_faceBoundaryTrail_leftRegion_eq
    (K : Set (Site 2)) (hK : K.Finite) {x y : Site 2}
    (hx : x ∈ K) (hy : y ∉ K)
    (hin : ∀ a b : Site 2, a ∈ K → b ∈ K →
      (latticeMinusBarrier K).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ K → b ∉ K →
      (latticeMinusBarrier K).Reachable a b) :
    ∃ (f : Site 2) (c : (faceBoundaryGraph K).Walk f f),
      c.IsTrail ∧
      (∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges) ∧
      K = jec_leftRegion (c.mapLe (faceBoundaryGraph_le K)) := by
  let T := phb_boundarySupport K hK
  have hconn : FaceBoundaryConnected K T :=
    faceBoundaryConnected_of_connected_complement K hK hx hy hin hout
  obtain ⟨w⟩ := pbs_reach_all x y
  obtain ⟨u, v, huv⟩ := walk_mem_edgeBoundary K w hx hy
  obtain ⟨f, g, hfg⟩ := exists_faceBoundaryGraph_adj_of_edgeBoundary K huv
  have hf : f ∈ (T : Set (Site 2)) := by
    simpa [T] using hfg.mem_support_left
  obtain ⟨c, htrail, hcover⟩ :=
    faceBoundaryGraph_single_dualCircuit
      (K := K) (T := T) (by intro z hz; simpa [T] using hz)
      hconn hf
  exact ⟨f, c, htrail, hcover,
    rlc_leftRegion_eq_of_faceBoundaryTrail K hK c htrail hcover⟩

end Universality
end StatMech

