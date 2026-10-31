/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorWitnessRemoveSite

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorWitnessRemoveSite`

In the plane:
* `bkm_cluster_removeSite_origin_eq_singleton` and `bkm_cluster_removeSite_origin_not_infinite`
  for the all-open configuration;
* `bkm_origin_no_neighbour` for the all-open configuration;
* `bkm_witness_ne_zero` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorWitnessRemoveSite

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-open configuration of the planar lattice. -/
def open2 : ConfigSpace (Sym2 (Site 2)) := fun _ => true

-- After removing the origin its cluster is `{0}`, and it is finite.
example : cluster 2 (removeSite 0 open2) 0 = {0} ∧
    ¬ (cluster 2 (removeSite 0 open2) 0).Infinite :=
  ⟨bkm_cluster_removeSite_origin_eq_singleton _, bkm_cluster_removeSite_origin_not_infinite _⟩

-- Even in the all-open configuration the removed origin has no open neighbour.
example : ¬ (openSubgraph 2 (removeSite 0 open2)).Adj 0 ![1, 0] :=
  bkm_origin_no_neighbour open2 _

-- Infinite cut-cluster witnesses are nonzero.
example (ω : ConfigSpace (Sym2 (Site 2))) (w : Site 2)
    (h : (cluster 2 (removeSite 0 ω) w).Infinite) : w ≠ 0 :=
  bkm_witness_ne_zero ω h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorWitnessRemoveSite
