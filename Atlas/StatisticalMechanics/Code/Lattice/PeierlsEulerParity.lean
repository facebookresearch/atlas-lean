/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.ClusterBoundaryRecovery

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin)











theorem bdEdge_eq_edgeStraddles (K : Set (Site 2)) (e : Sym2 (Site 2)) :
    bdEdge K e ↔ edgeStraddles K e := by
  refine Sym2.ind (fun x y => ?_) e
  rw [bdEdge_mk, edgeStraddles_mk]












theorem faceBoundaryGraph_adj_iff_boundaryEdgeSet (K : Set (Site 2)) (f g : Site 2) :
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


















theorem dualFace_incident_even (K : Set (Site 2)) (f : Site 2) :
    Even ((faceBoundaryGraph K).degree f) :=
  degree_faceBoundaryGraph_even K f





theorem dualFace_boundaryEdge_count_even (K : Set (Site 2)) (f : Site 2) :
    Even ((faceBoundaryGraph K).neighborFinset f).card := by
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  exact dualFace_incident_even K f
















theorem connCluster_dualFace_incident_even {K : Finset (Site 2)}
    (_hK : IsConnectedCluster K) (f : Site 2) :
    Even ((faceBoundaryGraph (↑K : Set (Site 2))).degree f) :=
  dualFace_incident_even (↑K : Set (Site 2)) f














theorem connCluster_contour_edge_on_cycle {K : Finset (Site 2)}
    (_hK : IsConnectedCluster K) {f g : Site 2}
    (hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u),
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph (↑K : Set (Site 2)) K.finite_toSet
  exact EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
    (faceBoundaryGraph (↑K : Set (Site 2))) T hT
    (degree_faceBoundaryGraph_even (↑K : Set (Site 2))) hadj















theorem faceBoundaryGraph_eq_of_boundaryEdgeSet_eq {K₁ K₂ : Set (Site 2)}
    (h : boundaryEdgeSet K₁ = boundaryEdgeSet K₂) :
    faceBoundaryGraph K₁ = faceBoundaryGraph K₂ := by
  ext f g
  rw [faceBoundaryGraph_adj_iff_boundaryEdgeSet, faceBoundaryGraph_adj_iff_boundaryEdgeSet, h]













theorem connCluster_evenContour_and_recovery {K : Finset (Site 2)}
    (hK : IsConnectedCluster K) :
    (∀ f : Site 2, Even ((faceBoundaryGraph (↑K : Set (Site 2))).degree f)) ∧
      (∀ x : Site 2, x ∈ (↑K : Set (Site 2)) ↔
        (latticeMinusBoundary (↑K : Set (Site 2))).Reachable (origin 2) x) :=
  ⟨fun f => connCluster_dualFace_incident_even hK f,
    fun x => connectedCluster_eq_component hK x⟩










theorem singletonOrigin_isConnectedCluster :
    IsConnectedCluster ({origin 2} : Finset (Site 2)) := by
  refine ⟨Finset.mem_singleton_self _, ?_⟩
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  exact SimpleGraph.Reachable.refl _


theorem origin_eq_zerozero : (origin 2) = (![0, 0] : Site 2) := by
  funext i; fin_cases i <;> rfl


theorem origin_mem_singleton_coe :
    (![0, 0] : Site 2) ∈ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  rw [Finset.mem_coe, Finset.mem_singleton, ← origin_eq_zerozero]


theorem one_zero_notMem_singleton_coe :
    (![1, 0] : Site 2) ∉ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  rw [Finset.mem_coe, Finset.mem_singleton]
  intro h
  have := congrFun h 0
  simp only [origin, Matrix.cons_val_zero] at this
  exact one_ne_zero this






theorem singleton_origin_dualFace_incident_even :
    (∀ f : Site 2,
        Even ((faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).degree f))
      ∧ ∃ f g : Site 2,
        (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj f g := by
  refine ⟨fun f => connCluster_dualFace_incident_even singletonOrigin_isConnectedCluster f, ?_⟩
  
  
  
  have hadj : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![0, 0] ![0, (0 : ℤ) - 1] := by
    rw [faceBoundaryGraph_adj]
    refine ⟨latAdj_bottom 0 0, ?_⟩
    rw [sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10
    rw [bdEdge_mk]
    refine ⟨fun _ => ?_, fun _ => origin_mem_singleton_coe⟩
    show (![(0 : ℤ) + 1, 0] : Site 2) ∉ _
    rw [show ((0 : ℤ) + 1) = 1 by ring]
    exact one_zero_notMem_singleton_coe
  exact ⟨_, _, hadj⟩

end Lattice

end StatMech
