/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxCutMerge

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxCutMerge`

* `bc117_cut_forceOpen_boxIncident` with the empty set of forced edges;
* `bc117_merge_of_le` at `L = 3`, `n = 2`;
* `bc117_engine_fires_upperLines` and `bc117_arm_shape_upperLines` on the upper-lines
  configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxCutMerge

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- Forcing no edge does not change the cut configuration.
example {d : ℕ} (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites T (forceOpenFinset ∅ ω) = removeSites T ω :=
  bc117_cut_forceOpen_boxIncident T ∅ ω (by simp)

-- Coarse trifurcations merge when the box radius is at most the scale.
example : bc115_CoarseTrifMerge 2 3 2 := bc117_merge_of_le (by norm_num)

-- The external-arm engine fires on the upper lines.
example := bc117_engine_fires_upperLines (h := 1) le_rfl 3

-- Three box-adjacent arms on the upper lines.
example := bc117_arm_shape_upperLines (L := 3) le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxCutMerge
