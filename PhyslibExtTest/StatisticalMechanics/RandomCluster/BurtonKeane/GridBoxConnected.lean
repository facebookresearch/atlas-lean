/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GridBoxConnected

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GridBoxConnected`

* `mem_boxEdges_iff`: the edge from the origin to `(1, 0)` is an edge of `B_1 ⊂ ℤ²` (instance).
* `box_allOpen_connected`: after opening the box edges of the all-closed configuration, the
  corners `(-1, -1)` and `(1, 1)` of `B_1` are connected (instance).
* `box_allOpen_cluster_eq`: they then have the same cluster.
* `mixSite` evaluates as the coordinate interpolation.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GridBoxConnected

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

/-- The corner `(-1, -1)` of `B_1`. -/
def c₀ : Site 2 := ![-1, -1]

/-- The corner `(1, 1)` of `B_1`. -/
def c₁ : Site 2 := ![1, 1]

/-- `(-1, -1)` lies in `B_1`. -/
theorem c₀_mem : c₀ ∈ box 2 1 := fun i => by fin_cases i <;> simp [c₀]

/-- `(1, 1)` lies in `B_1`. -/
theorem c₁_mem : c₁ ∈ box 2 1 := fun i => by fin_cases i <;> simp [c₁]

-- The edge from the origin to `(1, 0)` belongs to the box edges.
example : s((0 : Site 2), ![1, 0]) ∈ boxEdges 2 1 := by
  rw [mem_boxEdges_iff]
  refine ⟨fun i => by simp, fun i => by fin_cases i <;> simp, ?_⟩
  simp [Fin.sum_univ_two]

-- Opening the box connects opposite corners.
example : Connected 2 (forceOpenFinset (boxEdges 2 1) fun _ => false) c₀ c₁ :=
  box_allOpen_connected _ c₀_mem c₁_mem

-- ... so they have the same cluster.
example : cluster 2 (forceOpenFinset (boxEdges 2 1) fun _ => false) c₀ =
    cluster 2 (forceOpenFinset (boxEdges 2 1) fun _ => false) c₁ :=
  box_allOpen_cluster_eq _ c₀_mem c₁_mem

-- Interpolating one coordinate from `c₀` to `c₁` gives `(1, -1)`.
example : mixSite c₀ c₁ 1 = ![1, -1] := by
  funext i; fin_cases i <;> simp [mixSite, c₀, c₁]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GridBoxConnected
