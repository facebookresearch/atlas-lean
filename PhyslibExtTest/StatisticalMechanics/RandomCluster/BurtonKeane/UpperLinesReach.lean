/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.UpperLinesReach

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.UpperLinesReach`

* instance: `bc60_upperLines` has infinitely many infinite clusters and lies in `threeMeetBox 2 3`;
* the lines at heights `1` and `2` are distinct clusters (`bc60_cluster_ne`), the edge from `(0, 1)`
  to `(1, 1)` is open (`bc60_open`) and open paths keep their height (`bc60_height_invariant`);
* refutation: `bc60_not_disjointCorridors` and `bc60_not_hasDisjointCorridors`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.UpperLinesReach

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

-- Infinitely many infinite clusters, three of them meeting `B_3`.
example : numInfiniteClusters 2 bc60_upperLines = ⊤ ∧ bc60_upperLines ∈ threeMeetBox 2 3 :=
  ⟨bc60_numInfiniteClusters_top, bc60_mem_threeMeetBox⟩

-- Distinct heights give distinct clusters; horizontal edges at height one are open.
example : cluster 2 bc60_upperLines (bc57_pt 0 1) ≠ cluster 2 bc60_upperLines (bc57_pt 0 2) ∧
    bc60_upperLines s(bc57_pt 0 1, bc57_pt (0 + 1) 1) = true :=
  ⟨bc60_cluster_ne (by decide), bc60_open 0 le_rfl⟩

-- Open paths keep their height.
example (y : Site 2) (h : Connected 2 bc60_upperLines (bc57_pt 0 1) y) : y 1 = 1 :=
  bc60_height_invariant (by simp [bc57_pt]) h

-- No disjoint corridors: the corridor hypothesis fails in `ℤ²`.
example : ¬ bc59_DisjointCorridors bc60_upperLines ∧ ¬ bc59_HasDisjointCorridors 2 3 :=
  ⟨bc60_not_disjointCorridors, bc60_not_hasDisjointCorridors⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.UpperLinesReach
