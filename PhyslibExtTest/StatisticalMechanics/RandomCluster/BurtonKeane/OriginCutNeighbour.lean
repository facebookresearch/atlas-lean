/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutNeighbour

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutNeighbour`

* `bc4c_punctured_cluster_subset_neighbour_cutClusters` in the configuration of `ℤ²` whose only
  open edge is `{(0, 0), (1, 0)}`: the punctured cluster `{(1, 0)}` lies in the cut cluster of the
  open neighbour (instance).
* `bc4c_originCutLeavesInfinite` for the all-open configuration of `ℤ³` (instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutNeighbour

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The configuration of `ℤ²` whose only open edge is `{(0, 0), (1, 0)}`. -/
noncomputable def ω₁ : ConfigSpace (Sym2 (Site 2)) := fun e => decide (e = s(0, ![1, 0]))

/-- The edge `{(0, 0), (1, 0)}` is open in `ω₁`. -/
theorem ω₁_adj : (openSubgraph 2 ω₁).Adj 0 ![1, 0] := by simp [ω₁, Fin.sum_univ_two]

/-- `(1, 0)` is not the origin. -/
theorem e₀_ne : (![1, 0] : Site 2) ≠ 0 := fun h => by simpa using congrFun h 0

-- The site `(1, 0)` of the punctured cluster lies in a neighbour's cut cluster.
example : (![1, 0] : Site 2) ∈
    ⋃ n ∈ {n | (openSubgraph 2 ω₁).Adj 0 n}, cluster 2 (removeSite 0 ω₁) n :=
  bc4c_punctured_cluster_subset_neighbour_cutClusters ω₁ (x := 0) (connected_refl _ _)
    ⟨IsOpenEdge.connected ω₁_adj, e₀_ne⟩

-- The origin cut leaves an infinite piece in the all-open configuration of `ℤ³`.
example : bc3_OriginCutLeavesInfinite (d := 3) fun _ => true :=
  bc4c_originCutLeavesInfinite _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutNeighbour
