/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKDuality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKDuality`

* the inhomogeneous triangular surface vanishes at `q = 7`, odds `(2, 1, 1)` (`2 + 2 + 1 + 2 = 7`);
* `triangularFKCriticalSurface_iff_hexagonal_div` transports it to the hexagonal surface at the
  dual odds `(7/2, 7, 7)`;
* `fkEdgeOdds_mul_dualParam` at `p = 1/2`, `q = 4` (odds `1` and `4`), with `fkEdgeOdds (1/2) = 1`
  by evaluation;
* `triangularFKCriticalSurface_one_iff_isCriticalTri` turns the `q = 1` surface root at
  `p = (1/2, 1/2, 0)` into the percolation critical-surface predicate `IsCriticalTri`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKDuality

open _root_.StatMech.FK.TriHex _root_.StatMech.BeffaraDC

/-- An inhomogeneous triangular critical point at `q = 7`. -/
theorem tri_surface_seven : triangularFKCriticalSurface 7 2 1 1 = 0 := by
  norm_num [triangularFKCriticalSurface]

-- Its dual odds lie on the hexagonal surface.
example : hexagonalFKCriticalSurface 7 (7 / 2) (7 / 1) (7 / 1) = 0 :=
  (triangularFKCriticalSurface_iff_hexagonal_div (by norm_num) (by norm_num) one_ne_zero
    one_ne_zero).1 tri_surface_seven

-- `p = 1/2` has odds `1`.
example : fkEdgeOdds (1 / 2) = 1 := by
  norm_num [fkEdgeOdds]

-- The odds of `p` and its dual multiply to `q`.
example : fkEdgeOdds (1 / 2) * fkEdgeOdds (dualParam (1 / 2) 4) = 4 :=
  fkEdgeOdds_mul_dualParam (by norm_num) (by norm_num) (by norm_num)

-- The `q = 1` surface root `p = (1/2, 1/2, 0)` is a critical triangular percolation point.
example : _root_.StatMech.Universality.IsCriticalTri (1 / 2) (1 / 2) 0 :=
  (triangularFKCriticalSurface_one_iff_isCriticalTri (by norm_num) (by norm_num)
    (by norm_num)).1 (by norm_num [triangularFKCriticalSurface, fkEdgeOdds])

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKDuality
