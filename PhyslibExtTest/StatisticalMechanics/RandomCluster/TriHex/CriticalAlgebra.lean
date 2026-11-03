/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CriticalAlgebra

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CriticalAlgebra`

At cluster weight `q = 4` the triangular critical odds are `y = 1` (`1 + 3 - 4 = 0`) and the
hexagonal ones are `y* = 4` (`64 - 48 - 16 = 0`):
* `triangularFKCriticalPolynomial 4 1 = 0` and `hexagonalFKCriticalPolynomial 4 4 = 0` by
  evaluation (the polynomials are non-vacuous);
* `hexagonalFKCritical_div_of_triangular` produces the hexagonal root `4 / 1` from `y = 1`;
* `triangularFKCritical_iff_hexagonal_of_dual` transports the root back along `1 * 4 = 4`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.CriticalAlgebra

open _root_.StatMech.FK.TriHex

/-- `y = 1` is a triangular critical root at `q = 4`. -/
theorem tri_four_one : triangularFKCriticalPolynomial 4 1 = 0 := by
  norm_num [triangularFKCriticalPolynomial]

-- `y* = 4` is a hexagonal critical root at `q = 4`.
example : hexagonalFKCriticalPolynomial 4 4 = 0 := by
  norm_num [hexagonalFKCriticalPolynomial]

-- The dual odds `q / y` of the triangular root is a hexagonal root.
example : hexagonalFKCriticalPolynomial 4 (4 / 1) = 0 :=
  hexagonalFKCritical_div_of_triangular one_ne_zero tri_four_one

-- The duality equivalence applied at `y = 1`, `y* = 4`.
example : hexagonalFKCriticalPolynomial 4 4 = 0 :=
  (triangularFKCritical_iff_hexagonal_of_dual one_ne_zero (by norm_num) (by norm_num)).1
    tri_four_one

-- A non-root: `y = 2` is not a triangular critical root at `q = 4`.
example : triangularFKCriticalPolynomial 4 2 ≠ 0 := by
  norm_num [triangularFKCriticalPolynomial]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.CriticalAlgebra
