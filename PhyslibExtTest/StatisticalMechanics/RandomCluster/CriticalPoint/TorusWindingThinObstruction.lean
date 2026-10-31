/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusWindingThinObstruction

/-!
# Tests for
`PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusWindingThinObstruction`

* `windingThinCounterexample_winding_not_thin`: the explicit `8 × 8` configuration winds vertically
  but has no thin crossing;
* `not_bdcTorusVerticalWindingThinCover_two_one`: the thin-cover hypothesis is refuted at
  `(alpha, n) = (2, 1)`;
* `windingThinCounterexample_exists_missing` at `a = 0`, `c = 4`.

The module's `Fact` instances for `2 < 8` are local, so they are re-enabled here.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
namespace TorusWindingThinObstruction

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Lattice _root_.StatMech.RSW.Box

attribute [local instance] windingThinCounterexample_eightFact
  windingThinCounterexample_periodFact

-- The counterexample winds but does not cross thinly.
example : bdcTorusVerticalWinding 8 windingThinCounterexampleConfig ∧
    ¬ bdcTorusThinCrossing 8 2 1 windingThinCounterexampleConfig :=
  windingThinCounterexample_winding_not_thin

-- The thin-cover hypothesis at `(2, 1)` is false.
example : ¬ BdcTorusVerticalWindingThinCover 2 1 := not_bdcTorusVerticalWindingThinCover_two_one

-- A missing cut row in the window starting at column `0`, rows `4..7`.
example := windingThinCounterexample_exists_missing 0 4 le_rfl (by norm_num) (Or.inr rfl)

end TorusWindingThinObstruction
end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
