/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpness

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpness`

* the box root embeds as the black vertex at the origin (`hexagonalBoxEmbedding`, by `rfl`);
* `hexagonalBoxGraph_edgeSet_nonempty` at radius `1`;
* `hexagonalOuterInnerDenom_pos` at `n = 2`, `q = 2`, `β = 1`;
* `hexagonal_outer_inner_differential_logistic` at `n = 1`, `q = 1`, `β = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpness

open _root_.StatMech.FK.PeriodicPlanar

-- The root of the box is the black vertex at the origin.
example : hexagonalBoxEmbedding 1 (hexagonalBoxRoot 1) = (0, false) := rfl

-- The radius-`1` box has an edge.
example : Nonempty (hexagonalBoxGraph 1).edgeSet :=
  hexagonalBoxGraph_edgeSet_nonempty 1 le_rfl

-- The revealment denominator is positive.
example : 0 < hexagonalOuterInnerDenom 2 2 1 :=
  hexagonalOuterInnerDenom_pos 2 (by norm_num) 2 1 (by norm_num) one_pos

-- The logistic OSSS differential inequality at a concrete parameter point.
example : hexagonalOuterInnerTheta 1 1 1 * (1 - hexagonalOuterInnerTheta 1 1 1) /
      hexagonalOuterInnerDenom 1 1 1 ≤ hexagonalOuterInnerThetaPrime 1 1 1 :=
  hexagonal_outer_inner_differential_logistic 1 le_rfl 1 1 le_rfl one_pos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpness
