/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Coverage

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Coverage`

On the square lattice `square` at `p = 1/2`, `q = 1`:
* `bufferedTwoPointEvent_isIncreasing` feeds `freeBufferedInfiniteVolume_le_wired_cylinder` for the
  two-point event from `0` to `0` in the buffered box `0`;
* `HasInfiniteCluster` holds for the all-open configuration (non-vacuous), and
  `measurableSet_hasInfiniteCluster` applies to `square`;
* `freeDualHasInfiniteCluster_of_exponentialDecay` (needs a planar dual pair and
  `PolynomialConnectionShells`) elaborates (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Coverage

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

/-- The origin as a vertex of the buffered box `0`. -/
def origin : square.BufferedVertex 0 :=
  ⟨0, (square.mem_orbitBox_iff _ 0).2 ⟨0, by simp, 0, Finset.mem_singleton_self 0, by
    ext i; simp [square]⟩⟩

-- Free-below-wired comparison of the two-point cylinder at the origin.
example :
    (square.freeBufferedInfiniteVolume (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (square.bufferedCylinder 0 (square.bufferedTwoPointEvent 0 origin origin)) ≤
      (square.wiredBufferedInfiniteVolume (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (square.bufferedCylinder 0 (square.bufferedTwoPointEvent 0 origin origin)) :=
  square.freeBufferedInfiniteVolume_le_wired_cylinder 0 _ _ le_rfl
    (square.bufferedTwoPointEvent_isIncreasing 0 origin origin)

-- The all-open configuration has an infinite cluster.
example : square.HasInfiniteCluster allOpen := ⟨0, cluster_allOpen_infinite 0⟩

-- Having an infinite cluster is a measurable event on `square`.
example : MeasurableSet {ω : ConfigSpace (Sym2 (Site 2)) | square.HasInfiniteCluster ω} :=
  square.measurableSet_hasInfiniteCluster

-- The conditional dual-percolation headline elaborates.
example := @PeriodicPlanarDualPair.freeDualHasInfiniteCluster_of_exponentialDecay

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Coverage
