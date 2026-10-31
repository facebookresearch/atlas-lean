/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryForest`

In the plane:
* `bc66_status` gives the upper lines as a coarse trifurcation at `L = 3`;
* its leaf-count clause applies to the explicit caterpillar tree `bc65_cat2G`;
* its last clause gives disjoint boxes and an upper-lines connection at `L = 3`;
* `bc66_coarse_armReaching_unconditional` applies to the upper-lines right arm.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- The upper lines form a coarse trifurcation at the origin for `L = 3`.
example : bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  (bc66_status (d := 2)).2.1 le_rfl

-- Branch vertices of the six-vertex caterpillar are at most its leaves.
example : (Finset.univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card
    ≤ (Finset.univ.filter (fun v => bc65_cat2G.degree v = 1)).card :=
  (bc66_status (d := 2)).2.2.1 bc65_cat2G bc65_cat2G_isTree.isAcyclic bc65_cat2G_min_degree

-- Disjoint boxes and an upper-lines connection at `L = 3`.
example : Disjoint (bc61_boxAround 2 3 (0 : Site 2))
      (bc61_boxAround 2 3 (bc57_pt (2 * ((3 : ℕ) : ℤ) + 1) 0)) ∧
    Connected 2 bc60_upperLines (bc57_pt (((3 : ℕ) : ℤ) + 1) 1)
      (bc57_pt (2 * ((3 : ℕ) : ℤ) + 1 + (((3 : ℕ) : ℤ) + 1)) 1) :=
  (bc66_status (d := 2)).2.2.2.2 3

-- The upper-lines right arm at height `1` reaches the boundary of the radius-4 box.
example : ∃ z ∈ vertexBoundary 2 4,
    Connected 2 (removeSites (bc61_boxAround 2 3 0) bc60_upperLines)
      (bc57_pt (((3 : ℕ) : ℤ) + 1) 1) z :=
  bc66_coarse_armReaching_unconditional bc60_upperLines 3 4 (by norm_num) 0 _
    (by simp [box, Fin.forall_fin_two, bc57_pt]) (bc61_upperLines_rightArm_infinite le_rfl)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryForest
