/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromSecant

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKUniquenessClose3`

* `freeEdgeDensity` and `wiredEdgeDensity` (from `FKUniquenessFull`) are `0` outside
  `p ∈ (0, 1)`;
* `freeEdgeDensity_q2_le_wiredEdgeDensity` on `ℤ²` at `p = 1/2`: the free edge density is at most
  the wired one, for every edge of `Λ_1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKUniquenessClose3

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- The densities are set to `0` at `p = 1`.
example (e : Sym2 (Site 2)) : freeEdgeDensity 2 2 e 1 = 0 ∧ wiredEdgeDensity 2 2 e 1 = 0 := by
  simp [freeEdgeDensity, wiredEdgeDensity]

-- Free density `≤` wired density at `p = 1/2`, for an edge of `Λ_1`.
example (eb : Sym2 (boxVerts 2 1)) :
    freeEdgeDensity 2 2 (edgeIncl 2 1 eb) (1 / 2)
      ≤ wiredEdgeDensity 2 2 (edgeIncl 2 1 eb) (1 / 2) :=
  freeEdgeDensity_q2_le_wiredEdgeDensity 2 1 eb (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKUniquenessClose3
