/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxTrifSet

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxTrifSet`

* `bfin2_trifSet_finite` and `bfin2_count` on the all-closed configuration of `ℤ²` with `R = 2`
  (instance): the fine-trifurcation set of `B_1` is finite and at most `|∂B_2|`.
* The same count for the upper-lines configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxTrifSet

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The fine-trifurcation set of the all-closed configuration is finite.
example : {x : Site 2 | bft_FineTrif (fun _ => false) x ∧ x ∈ box 2 (2 - 1)}.Finite :=
  bfin2_trifSet_finite _ 2

-- Its size is at most the boundary size.
example : (bfin2_trifSet_finite (d := 2) (fun _ => false) 2).toFinset.card ≤
    (vertexBoundary_finite 2 2).toFinset.card :=
  bfin2_count _ 2 (by norm_num)

-- The same bound for the upper-lines configuration.
example : (bfin2_trifSet_finite bc60_upperLines 3).toFinset.card ≤
    (vertexBoundary_finite 2 3).toFinset.card :=
  bfin2_count _ 3 (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.NeighbourBoxTrifSet
