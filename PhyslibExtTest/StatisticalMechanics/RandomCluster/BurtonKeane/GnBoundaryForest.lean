/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnBoundaryForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnBoundaryForest`

* The third conjunct of `bc68_status` at `L = 2`: two disjoint boxes on the upper-lines
  configuration are joined by the first upper line, so arms of two trifurcations can share
  boundary sites (instance).
* `bc68_Gn_singleTrif_distinct_leaves` and `bc68_coarseTcount_le_boundary_of_GnForestData` as
  conditional statements.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnBoundaryForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The boxes around `(0, 0)` and `(5, 0)` are disjoint, but the first upper line joins them.
example : Disjoint (bc61_boxAround 2 2 (0 : Site 2)) (bc61_boxAround 2 2 (bc57_pt (2 * 2 + 1) 0)) ∧
    Connected 2 bc60_upperLines (bc57_pt ((2 : ℕ) + 1) 1)
      (bc57_pt (2 * (2 : ℕ) + 1 + ((2 : ℕ) + 1)) 1) := by
  simpa using (bc68_status (d := 2)).2.2 2

-- Three separated arms reach three distinct boundary sites.
example (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2) (a z : Fin 3 → Site 2)
    (h01 : ¬ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) (a 0) (a 1))
    (h02 : ¬ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) (a 0) (a 2))
    (h12 : ¬ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) (a 1) (a 2))
    (hr : ∀ i, (bc67_contractedLattice ω L y).Reachable (a i) (z i)) : Function.Injective z :=
  bc68_Gn_singleTrif_distinct_leaves ω L y a h01 h02 h12 z hr

-- Forest data bound the coarse count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bc68_GnForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bc68_coarseTcount_le_boundary_of_GnForestData ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnBoundaryForest
