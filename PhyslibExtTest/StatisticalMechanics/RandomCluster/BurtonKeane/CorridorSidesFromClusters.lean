/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters`

In the plane:
* `csc_clusters_disjoint`: distinct sites of the all-closed configuration have disjoint clusters;
* `csc_cluster_adjClosed` for the all-closed configuration;
* `csc_disjointCorridorRouting_of_distinctClusters` and `csc_corridorCover_of_distinctClusters` in
  conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Percolation.DisjointPaths

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-closed configuration only a site is connected to itself. -/
theorem closed_connected_eq {a b : Site 2} (h : Connected 2 closed2 a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [closed2])

/-- Distinct sites have distinct clusters in the all-closed configuration. -/
theorem closed_cluster_ne {a b : Site 2} (hab : a ≠ b) :
    cluster 2 closed2 a ≠ cluster 2 closed2 b := by
  intro h
  have hb : b ∈ cluster 2 closed2 b := SimpleGraph.Reachable.refl b
  rw [← h] at hb
  exact hab (closed_connected_eq hb)

-- The clusters of the origin and of `(1, 0)` in the all-closed configuration are disjoint.
example : Disjoint (cluster 2 closed2 0) (cluster 2 closed2 ![1, 0]) :=
  csc_clusters_disjoint closed2 fun h => by simpa using congrFun (closed_connected_eq h) 0

-- Clusters are closed under open adjacency.
example (u v : Site 2) (hu : u ∈ cluster 2 closed2 0) (h : (openSubgraph 2 closed2).Adj u v) :
    v ∈ cluster 2 closed2 0 :=
  csc_cluster_adjClosed closed2 0 u v hu h

-- Distinct-cluster corridors give a disjoint corridor routing.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : csc_DistinctClusterCorridors ω) :
    DisjointCorridorRouting ω :=
  csc_disjointCorridorRouting_of_distinctClusters ω h

-- And, on a whole three-meet event, a corridor cover.
example (n : ℕ) (h : ∀ ω ∈ threeMeetBox 2 n, csc_DistinctClusterCorridors ω) :
    threeMeetBox 2 n ⊆
      ⋃ (a₁ : Site 2) (a₂ : Site 2) (a₃ : Site 2) (G : Finset (Sym2 (Site 2))),
        CorridorWorks a₁ a₂ a₃ G :=
  csc_corridorCover_of_distinctClusters h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorSidesFromClusters
