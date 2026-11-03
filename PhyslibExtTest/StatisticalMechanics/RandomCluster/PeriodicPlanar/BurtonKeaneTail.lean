/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTail

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTail`

On the square lattice `square` with the all-open configuration (whose clusters are all of `ℤ²`)
and `K = {0}`:
* `infiniteCluster_component_after_finset` gives an infinite component of the cluster minus `K`;
* `infiniteCluster_has_open_exit` gives tail data (`InfiniteTailData` is non-vacuous);
* the exit edge of `infiniteTailData` starts at `0`, the only vertex of `K`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTail

open MeasureTheory _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-open configuration every cluster is the whole lattice. -/
theorem cluster_allOpen (x : Site 2) : square.cluster allOpen x = Set.univ := by
  have hopen : square.openSubgraph allOpen = hypercubicLattice 2 := by
    ext a b
    simp only [PeriodicGraph.openSubgraph_adj, allOpen, and_true]
    rfl
  ext y
  simp only [PeriodicGraph.cluster, hopen, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hypercubicLattice_two_reachable x y

/-- The cluster of every vertex in the all-open configuration is infinite. -/
theorem cluster_allOpen_infinite (x : Site 2) : (square.cluster allOpen x).Infinite := by
  rw [cluster_allOpen]; exact Set.infinite_univ

-- Removing `{0}` from the infinite all-open cluster of `0` leaves an infinite component.
example : ∃ D : (square.tailClusterGraph allOpen 0).ComponentCompl
    (square.tailClusterCut allOpen 0 {0}), D.supp.Infinite :=
  square.infiniteCluster_component_after_finset allOpen 0 (cluster_allOpen_infinite 0) {0}

-- The all-open cluster of `0` has an open exit from `{0}` into an infinite tail.
example : Nonempty (square.InfiniteTailData allOpen {0} 0) :=
  square.infiniteCluster_has_open_exit allOpen 0 (cluster_allOpen_infinite 0) {0}
    (Finset.mem_singleton_self 0)

-- The exit edge starts inside `K = {0}`, hence at `0`.
example : (square.infiniteTailData allOpen 0 (cluster_allOpen_infinite 0) {0}
    (Finset.mem_singleton_self 0)).inside = 0 :=
  Finset.mem_singleton.mp (PeriodicGraph.InfiniteTailData.inside_mem _)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneTail
