/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.RSWLowestCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.RSWLowestCrossing`

* `rlc_square_half` at `m = 3`: `1/2 ≤ P(horizontal crossing of [0, 3]²)` (unconditional);
* `rlc_half_rightDiagonal_unconditional` and `rlc_half_leftDiagonal_unconditional` at `n = 2`
  (`1/32` lower bounds);
* `rlc_mixedWiredConnector_half_of_dual_reflection` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.RSWLowestCrossing

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.RSW.Box _root_.StatMech.Universality

-- Square crossing at `p = 1/2`.
example : (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent 0 3 0 3) :=
  rlc_square_half 3 (by norm_num)

-- The right diagonal event has probability at least `1/32`.
example : (1 : ℝ) / 32 ≤ halfMeasure.real (rlc_rightDiagonal 2) :=
  rlc_half_rightDiagonal_unconditional 2 (by norm_num)

-- The left diagonal event has probability at least `1/32`.
example : (1 : ℝ) / 32 ≤ halfMeasure.real (rlc_leftDiagonal 2) :=
  rlc_half_leftDiagonal_unconditional 2 (by norm_num)

-- The connector bound, given the dual-reflection hypothesis.
example {n : ℤ} {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdual : ∀ omega : ConfigSpace (Sym2 (Site 2)), omega ∉ rlc_mixedWiredConnectorEvent G →
      rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (rlc_mixedWiredConnectorEvent G) :=
  rlc_mixedWiredConnector_half_of_dual_reflection G hdual

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.RSWLowestCrossing
