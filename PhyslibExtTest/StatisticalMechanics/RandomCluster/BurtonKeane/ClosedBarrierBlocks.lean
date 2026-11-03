/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedBarrierBlocks

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedBarrierBlocks`

* `bc3_barrier_blocks` with the barrier `{0}` in the all-closed configuration of `ℤ²`;
* `bc3_barrier_blocks_iff_cluster` in the backward direction with the same barrier;
* `bc3_cluster_adjClosed` for the all-open configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedBarrierBlocks

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

/-- In the all-closed configuration every set is closed under open adjacency. -/
theorem adjClosed_closed (R : Set (Site 2)) : bc3_AdjClosed (fun _ => false) R :=
  fun _ _ _ h => absurd h.2 (by simp)

/-- The unit vector `e₀` of `ℤ²` is not the origin. -/
theorem e0_ne : (Pi.single 0 1 : Site 2) ∉ ({0} : Set (Site 2)) := by
  intro h
  simpa using congrFun (Set.mem_singleton_iff.mp h) 0

-- The barrier `{0}` blocks the origin from `e₀`.
example : ¬ Connected 2 (fun _ => false) 0 (Pi.single 0 1) :=
  bc3_barrier_blocks _ {0} 0 _ (adjClosed_closed _) rfl e0_ne

-- The same, via the barrier characterization.
example : ¬ Connected 2 (fun _ => false) 0 (Pi.single 0 1) :=
  (bc3_barrier_blocks_iff_cluster _ _ _).mpr ⟨{0}, adjClosed_closed _, rfl, e0_ne⟩

-- Clusters are closed under open adjacency.
example (w : Site 2) : bc3_AdjClosed (fun _ => true) (cluster 2 (fun _ => true) w) :=
  bc3_cluster_adjClosed _ w

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedBarrierBlocks
