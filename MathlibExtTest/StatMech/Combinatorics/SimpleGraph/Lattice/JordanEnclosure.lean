/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosure

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosure`

Instantiates `exists_dualCircuit_of_finite_cluster` at the configuration of `ℤ²` with every bond
closed: the cluster of the origin is `{0}`, the walk is the single edge from `0` to `(1, 0)`, and
the conclusion is a cycle of faces around the origin in `faceBoundaryGraph {0}`. Applies
`exists_cycle_through_edge_of_even` to the complete graph on `Fin 3` (all degrees two). Computes
`bdEdge {0}` on two edges and applies `degree_faceBoundaryGraph_even` at the origin.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanEnclosure

open _root_.StatMech _root_.StatMech.Lattice

/-- The configuration with every bond closed. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

theorem cluster_allClosed (o : Site 2) : cluster 2 allClosed o = {o} := by
  have h : openSubgraph 2 allClosed = ⊥ := by
    ext x y; simp [openSubgraph_adj, allClosed]
  ext y
  simp only [mem_cluster, Connected, h, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

-- `bdEdge {0}`: the edge `0 - (1, 0)` has exactly one endpoint in `{0}`, `(1,0) - (2,0)` none.
example : bdEdge {![0, 0]} s(![0, 0], ![1, 0]) := by
  simp [funext_iff, Fin.forall_fin_two]

example : ¬ bdEdge {![0, 0]} s(![1, 0], ![2, 0]) := by
  simp [funext_iff, Fin.forall_fin_two]

-- `exists_dualCircuit_of_finite_cluster`: the closed bonds around the origin give a cycle of
-- faces in the face-boundary graph of its cluster.
example : ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 allClosed ![0, 0])).Walk u u),
    c.IsCycle := by
  have hadj : (hypercubicLattice 2).Adj ![0, 0] ![1, 0] := by simp [Fin.sum_univ_two]
  refine exists_dualCircuit_of_finite_cluster (ω := allClosed) ![0, 0] ?_ hadj.toWalk ?_
  · rw [cluster_allClosed]; exact Set.finite_singleton _
  · rw [cluster_allClosed]; simp [funext_iff, Fin.forall_fin_two]

-- The cycle has length at least four (every cycle in the square lattice does; here we only
-- extract the general bound `3 ≤ length` from `IsCycle`).
example : ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 allClosed ![0, 0])).Walk u u),
    3 ≤ c.length := by
  have hadj : (hypercubicLattice 2).Adj ![0, 0] ![1, 0] := by simp [Fin.sum_univ_two]
  obtain ⟨u, c, hc⟩ := exists_dualCircuit_of_finite_cluster (ω := allClosed) ![0, 0]
    (by rw [cluster_allClosed]; exact Set.finite_singleton _) hadj.toWalk
    (by rw [cluster_allClosed]; simp [funext_iff, Fin.forall_fin_two])
  exact ⟨u, c, hc.three_le_length⟩

-- `exists_cycle_through_edge_of_even`: in the triangle every degree is two, so the edge `0 - 1`
-- lies on a cycle.
example : ∃ (u : Fin 3) (c : (⊤ : SimpleGraph (Fin 3)).Walk u u),
    c.IsCycle ∧ s(0, 1) ∈ c.edges := by
  have heven : ∀ x, Even ((⊤ : SimpleGraph (Fin 3)).degree x) := by decide
  exact EvenDegree.exists_cycle_through_edge_of_even (⊤ : SimpleGraph (Fin 3)) heven
    (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1)

-- `degree_faceBoundaryGraph_even` at the face `(0, 0)` of the boundary of `{0}`.
example : Even ((faceBoundaryGraph {![0, 0]}).degree ![0, 0]) :=
  degree_faceBoundaryGraph_even _ _

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanEnclosure
