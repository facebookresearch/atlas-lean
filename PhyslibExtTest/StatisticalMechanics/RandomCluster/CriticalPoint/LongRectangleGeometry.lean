/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleGeometry

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleGeometry`

* `bdcLongRectanglePeriod 1 3 = 6` and `bdcLongRectangleIndices_card` at `alpha = 2` (`16`
  translates);
* `bdcLongRectangleEvent_probability_eq_selfDual`: translates have equal probability under
  `halfMeasure`;
* `bdcLongRectangle_polynomial_deficit` for `halfMeasure` with `c = 1`, `ε = 0` (the union
  hypothesis holds trivially), reduced to positive association;
* `bdcLongRectangleUnion_isIncreasing`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleGeometry

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Universality MeasureTheory

-- The period of the long-rectangle family.
example : bdcLongRectanglePeriod 1 3 = 6 := rfl

-- There are `2 α³` translates.
example : (bdcLongRectangleIndices 2).card = 16 := bdcLongRectangleIndices_card 2

-- Translates have the same crossing probability at `p = 1/2`.
example (k : BdcLongRectangleIndex 2) :=
  bdcLongRectangleEvent_probability_eq_selfDual 2 5 k

-- The polynomial deficit bound for `halfMeasure`, given positive association.
example (hpa : PositivelyAssociated halfMeasure) :=
  bdcLongRectangle_polynomial_deficit halfMeasure hpa cti_selfDual_shift_invariant
    (alpha := 1) (n := 2) one_pos (by norm_num) (c := 1) (epsilon := 0) zero_le_one
    (by simp)

-- The union of translates is increasing.
example := bdcLongRectangleUnion_isIncreasing 2 5

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleGeometry
