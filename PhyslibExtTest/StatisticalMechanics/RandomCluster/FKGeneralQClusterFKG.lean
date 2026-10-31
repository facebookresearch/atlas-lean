/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQClusterFKG

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQClusterFKG`

* `fkgq_freeInfiniteVolume_clusterInfinite_fkg` at `p = 1/2`, `q = 1` (Bernoulli percolation)
  and at `q = 2` (FK-Ising), for the origin with itself and for two distinct sites.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQClusterFKG

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- Infinite-cluster events at the origin are positively correlated at `q = 1`.
example := fkgq_freeInfiniteVolume_clusterInfinite_fkg (p := 1 / 2) (q := 1) (by norm_num)
  (by norm_num) le_rfl 0 0

-- At `q = 2`, for the origin and the site `(1, 0)`.
example := fkgq_freeInfiniteVolume_clusterInfinite_fkg (p := 1 / 2) (q := 2) (by norm_num)
  (by norm_num) one_le_two 0 ![1, 0]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKGeneralQClusterFKG
