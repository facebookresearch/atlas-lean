/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Peierls.ClusterBoundaryRecovery
public import PhyslibExt.CondensedMatter.IsingModel.Peierls.PeierlsBoundaryConnected

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Peierls.ClusterBoundaryRecovery`

* `boundaryEdgeSet` of the empty set is empty;
* `connectedCluster_eq_component` for the singleton `{0}`: the origin is reachable from itself in
  the lattice minus `∂{0}`;
* `boundaryEdgeSet_injective` on two distinct connected clusters, the singleton `{0}` and the
  segment `boxCluster 1 0 = {(0, 0), (1, 0)}`: their edge boundaries differ.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Peierls.ClusterBoundaryRecovery

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Ising

-- No edge straddles the empty set.
example : boundaryEdgeSet (∅ : Set (Site 2)) = ∅ := by
  ext e
  simp only [boundaryEdgeSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  induction e using Sym2.ind with
  | _ x y => simp [edgeStraddles]

-- The origin lies in its own component of the lattice minus `∂{0}`.
example : (latticeMinusBoundary (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Reachable
    (origin 2) (origin 2) :=
  (connectedCluster_eq_component singleton_origin_isConnectedCluster (origin 2)).mp
    (by simp)

-- Distinct connected clusters have distinct edge boundaries.
example : boundaryEdgeSet (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ≠
    boundaryEdgeSet (↑(boxCluster 1 0) : Set (Site 2)) := by
  intro h
  have hK := boundaryEdgeSet_injective (d := 2) singleton_origin_isConnectedCluster
    (boxCluster_isConnectedCluster 1 0) h
  have hmem : (![1, 0] : Site 2) ∈ boxCluster 1 0 := by rw [mem_boxCluster]; simp
  rw [← hK, Finset.mem_singleton] at hmem
  have := congrFun hmem 0
  simp [origin] at this

end PhyslibExtTest.CondensedMatter.IsingModel.Peierls.ClusterBoundaryRecovery
