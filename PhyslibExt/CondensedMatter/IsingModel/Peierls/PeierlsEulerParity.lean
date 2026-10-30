/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import MathlibExt.Probability.Configuration.ConfigSpace
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanZ2
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosure
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.ClusterBoundaryRecovery
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.ContourCountInjection
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingParity

/-!
# Parity of the dual contour graph of a planar cluster

In `ℤ²`, every dual face meets an even number of contour edges of a set of sites, so every edge
of the contour of a connected cluster lies on a dual cycle.

## i. Overview

For `K ⊆ ℤ²`, the face-boundary graph joins two adjacent dual faces when the primal edge between
them straddles `K`. Its adjacency is exactly membership of the shared primal edge in the edge
boundary `∂K` of `ClusterBoundaryRecovery`, and around each face the number of straddling edges
is even. Hence all degrees are even, every contour edge lies on a cycle, and the face-boundary
graph depends only on `∂K`. For the singleton cluster `{0}` the contour is nonempty.

## ii. Key results

- `faceBoundaryGraph_adj_iff_boundaryEdgeSet` : dual adjacency is membership in `∂K`.
- `dualFace_incident_even` : every dual face has even degree.
- `connCluster_contour_edge_on_cycle` : every contour edge of a connected cluster lies on a
  dual cycle.
- `connCluster_evenContour_and_recovery` : even contour degrees together with recovery of the
  cluster from `∂K`.

## iii. Table of contents

- A. Dual adjacency and the edge boundary
- B. Even degrees and cycles
- C. The singleton cluster

## iv. References

- R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936)
  477–481.
- R. B. Griffiths, *Peierls proof of spontaneous magnetization in a two-dimensional Ising
  ferromagnet*, Phys. Rev. 136 (1964) A437–A439.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.7.2.
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin)

/-! ## A. Dual adjacency and the edge boundary -/

lemma bdEdge_eq_edgeStraddles (K : Set (Site 2)) (e : Sym2 (Site 2)) :
    bdEdge K e ↔ edgeStraddles K e := by
  refine Sym2.ind (fun x y => ?_) e
  rw [bdEdge_mk, edgeStraddles_mk]

lemma faceBoundaryGraph_adj_iff_boundaryEdgeSet (K : Set (Site 2)) (f g : Site 2) :
    (faceBoundaryGraph K).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∈ boundaryEdgeSet K := by
  rw [faceBoundaryGraph_adj]
  constructor
  · rintro ⟨hadj, hbd⟩
    obtain ⟨p, q, hpq, hpqadj⟩ := sharedPrimalEdge_isLatticeEdge hadj
    refine ⟨hadj, ?_⟩
    rw [bdEdge_eq_edgeStraddles] at hbd
    rw [hpq] at hbd ⊢
    exact (edgeStraddles_iff_mem_boundaryEdgeSet K hpqadj).mp hbd
  · rintro ⟨hadj, hmem⟩
    obtain ⟨p, q, hpq, hpqadj⟩ := sharedPrimalEdge_isLatticeEdge hadj
    refine ⟨hadj, ?_⟩
    rw [bdEdge_eq_edgeStraddles]
    rw [hpq] at hmem ⊢
    exact (edgeStraddles_iff_mem_boundaryEdgeSet K hpqadj).mpr hmem

/-! ## B. Even degrees and cycles -/

lemma dualFace_incident_even (K : Set (Site 2)) (f : Site 2) :
    Even ((faceBoundaryGraph K).degree f) :=
  degree_faceBoundaryGraph_even K f

lemma connCluster_dualFace_incident_even {K : Finset (Site 2)}
    (_hK : IsConnectedCluster K) (f : Site 2) :
    Even ((faceBoundaryGraph (↑K : Set (Site 2))).degree f) :=
  dualFace_incident_even (↑K : Set (Site 2)) f

lemma connCluster_contour_edge_on_cycle {K : Finset (Site 2)}
    (_hK : IsConnectedCluster K) {f g : Site 2}
    (hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u),
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph (↑K : Set (Site 2)) K.finite_toSet
  exact EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
    (faceBoundaryGraph (↑K : Set (Site 2))) T hT
    (degree_faceBoundaryGraph_even (↑K : Set (Site 2))) hadj

lemma faceBoundaryGraph_eq_of_boundaryEdgeSet_eq {K₁ K₂ : Set (Site 2)}
    (h : boundaryEdgeSet K₁ = boundaryEdgeSet K₂) :
    faceBoundaryGraph K₁ = faceBoundaryGraph K₂ := by
  ext f g
  rw [faceBoundaryGraph_adj_iff_boundaryEdgeSet, faceBoundaryGraph_adj_iff_boundaryEdgeSet, h]

lemma connCluster_evenContour_and_recovery {K : Finset (Site 2)}
    (hK : IsConnectedCluster K) :
    (∀ f : Site 2, Even ((faceBoundaryGraph (↑K : Set (Site 2))).degree f)) ∧
      (∀ x : Site 2, x ∈ (↑K : Set (Site 2)) ↔
        (latticeMinusBoundary (↑K : Set (Site 2))).Reachable (origin 2) x) :=
  ⟨fun f => connCluster_dualFace_incident_even hK f,
    fun x => connectedCluster_eq_component hK x⟩

/-! ## C. The singleton cluster -/

lemma origin_eq_zerozero : (origin 2) = (![0, 0] : Site 2) := by
  funext i; fin_cases i <;> rfl

lemma origin_mem_singleton_coe :
    (![0, 0] : Site 2) ∈ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  rw [Finset.mem_coe, Finset.mem_singleton, ← origin_eq_zerozero]

lemma one_zero_notMem_singleton_coe :
    (![1, 0] : Site 2) ∉ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  rw [Finset.mem_coe, Finset.mem_singleton]
  intro h
  have := congrFun h 0
  simp only [origin, Matrix.cons_val_zero] at this
  exact one_ne_zero this

lemma singleton_origin_dualFace_incident_even :
    (∀ f : Site 2,
        Even ((faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).degree f))
      ∧ ∃ f g : Site 2,
        (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj f g := by
  refine ⟨fun f => connCluster_dualFace_incident_even singleton_origin_isConnectedCluster f, ?_⟩
  have hadj : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![0, 0] ![0, (0 : ℤ) - 1] := by
    rw [faceBoundaryGraph_adj]
    refine ⟨latAdj_bottom 0 0, ?_⟩
    rw [sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10
    rw [bdEdge_mk]
    refine ⟨fun _ => ?_, fun _ => origin_mem_singleton_coe⟩
    change (![(0 : ℤ) + 1, 0] : Site 2) ∉ _
    rw [show ((0 : ℤ) + 1) = 1 by ring]
    exact one_zero_notMem_singleton_coe
  exact ⟨_, _, hadj⟩

end Lattice

end StatMech
