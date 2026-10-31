/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourCutCluster

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourCutCluster`

* `bc9nbr_mem_neighbour_cutCluster_of_adj` in the configuration of `ℤ²` whose only open edge is
  `{(0, 0), (1, 0)}`: the open neighbour `(1, 0)` lies in the cut cluster of an open neighbour of
  the origin (instance).
* `bc9nbr_mem_neighbour_cutCluster` for the same site, from the connection `0 ↔ (1, 0)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourCutCluster

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The configuration of `ℤ²` whose only open edge is `{(0, 0), (1, 0)}`. -/
noncomputable def ω₁ : ConfigSpace (Sym2 (Site 2)) := fun e => decide (e = s(0, ![1, 0]))

/-- The edge `{(0, 0), (1, 0)}` is open in `ω₁`. -/
theorem ω₁_adj : (openSubgraph 2 ω₁).Adj 0 ![1, 0] := by simp [ω₁, Fin.sum_univ_two]

/-- `(1, 0)` is not the origin. -/
theorem e₀_ne : (![1, 0] : Site 2) ≠ 0 := fun h => by simpa using congrFun h 0

-- The open neighbour lies in the cut cluster of an open neighbour.
example : ∃ n, (openSubgraph 2 ω₁).Adj 0 n ∧ ![1, 0] ∈ cluster 2 (removeSite 0 ω₁) n :=
  bc9nbr_mem_neighbour_cutCluster_of_adj _ e₀_ne ω₁_adj

-- The same from the open connection.
example : ∃ n, (openSubgraph 2 ω₁).Adj 0 n ∧ ![1, 0] ∈ cluster 2 (removeSite 0 ω₁) n :=
  bc9nbr_mem_neighbour_cutCluster _ e₀_ne (IsOpenEdge.connected ω₁_adj)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourCutCluster
