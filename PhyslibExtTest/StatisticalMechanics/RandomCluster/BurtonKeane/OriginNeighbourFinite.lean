/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginNeighbourFinite

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginNeighbourFinite`

* `bc4_origin_latticeNeighbours_ncard_le`: the origin of `ℤ²` has at most four lattice neighbours
  (instance).
* `bc4_origin_openNeighbours_ncard_le` for the all-open configuration.
* `bc4_nbrKey_injOn` in `ℤ³`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginNeighbourFinite

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Walls

-- At most four lattice neighbours in `ℤ²`.
example : {n : Site 2 | (hypercubicLattice 2).Adj 0 n}.ncard ≤ 4 :=
  bc4_origin_latticeNeighbours_ncard_le

-- At most four open neighbours in the all-open configuration.
example : {n : Site 2 | (openSubgraph 2 fun _ => true).Adj 0 n}.ncard ≤ 2 * 2 :=
  bc4_origin_openNeighbours_ncard_le _

-- The coordinate-and-sign key is injective on lattice neighbours.
example : Set.InjOn bc4_nbrKey {n : Site 3 | (hypercubicLattice 3).Adj 0 n} :=
  bc4_nbrKey_injOn

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginNeighbourFinite
