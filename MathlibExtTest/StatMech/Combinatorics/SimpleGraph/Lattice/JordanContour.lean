/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanContour

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanContour`

Instantiates the discrete Jordan separation theorems `discrete_jordan_separation` and
`discrete_jordan_components` at the configuration of `ℤ²` with every bond closed, where the cluster
of the origin is `{0}` (finite, so the hypothesis holds). From the conclusions it derives that the
origin cannot reach its neighbour `(1, 0)` in the lattice with the boundary edges of `{0}` removed,
that the inside component is finite and differs from the infinite outside component, and that two
far exterior sites are connected. The adjacency of `latticeMinusBarrier {0}` is also computed.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanContour

open _root_.StatMech _root_.StatMech.Lattice

/-- The configuration with every bond closed. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- With every bond closed, the cluster of a site is that site. -/
theorem cluster_allClosed (o : Site 2) : cluster 2 allClosed o = {o} := by
  have h : openSubgraph 2 allClosed = ⊥ := by
    ext x y; simp [openSubgraph_adj, allClosed]
  ext y
  simp only [mem_cluster, Connected, h, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

theorem cluster_allClosed_finite (o : Site 2) : (cluster 2 allClosed o).Finite := by
  rw [cluster_allClosed]; exact Set.finite_singleton o

-- `latticeMinusBarrier {0}` removes the edge `0 - (1, 0)` but keeps `(1, 0) - (1, 1)`.
example : ¬ (latticeMinusBarrier ({![0, 0]} : Set (Site 2))).Adj ![0, 0] ![1, 0] := by
  simp [latticeMinusBarrier]

example : (latticeMinusBarrier ({![0, 0]} : Set (Site 2))).Adj ![1, 0] ![1, 1] := by
  simp [latticeMinusBarrier, Fin.sum_univ_two, funext_iff, Fin.forall_fin_two]

-- `discrete_jordan_separation`: the origin, surrounded by its closed bonds, cannot reach `(1, 0)`
-- once the boundary edges of its cluster are removed.
example : ¬ (latticeMinusBarrier (cluster 2 allClosed ![0, 0])).Reachable ![0, 0] ![1, 0] := by
  obtain ⟨_, _, _, _, hsep⟩ :=
    discrete_jordan_separation (ω := allClosed) ![0, 0] (cluster_allClosed_finite _)
  refine hsep ?_ ?_
  · rw [cluster_allClosed]; rfl
  · rw [cluster_allClosed]; simp [funext_iff, Fin.forall_fin_two]

-- `discrete_jordan_separation`: two sites outside the enclosing box are connected.
example : ∃ R : ℕ, ∀ x y : Site 2, x ∈ exterior 2 R → y ∈ exterior 2 R →
    (latticeMinusBarrier (cluster 2 allClosed ![0, 0])).Reachable x y := by
  obtain ⟨R, _, _, hout, _⟩ :=
    discrete_jordan_separation (ω := allClosed) ![0, 0] (cluster_allClosed_finite _)
  exact ⟨R, fun x y hx hy => hout hx hy⟩

-- `discrete_jordan_components`: a finite inside component, an infinite outside one, distinct.
example : ∃ Cin Cout : (latticeMinusBarrier (cluster 2 allClosed ![0, 0])).ConnectedComponent,
    Cin.supp.Finite ∧ Cout.supp.Infinite ∧ Cin ≠ Cout ∧ (![0, 0] : Site 2) ∈ Cin.supp := by
  obtain ⟨R, _, Cin, Cout, hin, _, hfin, hinf, hne, hcl, _⟩ :=
    discrete_jordan_components (ω := allClosed) ![0, 0] (cluster_allClosed_finite _)
  refine ⟨Cin, Cout, hfin, hinf, hne, ?_⟩
  rw [hin]; rfl

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanContour
