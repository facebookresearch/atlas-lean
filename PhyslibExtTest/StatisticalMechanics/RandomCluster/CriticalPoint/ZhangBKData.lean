/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangBKData

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangBKData`

* `zbd_atLeastTwo_halfMeasure_zero`: at most one infinite cluster at `p = 1/2` (Burton–Keane);
* `zbd_twoScaleError_tendsto_zero` for the centered left and right sides of the unit box;
* `zbd_centeredMerge_subset_horizontalCrossing` at `n = 1`, `M = 2`;
* `zbd_boxHitsInfinite_tendsto_one` in conditional form (it assumes `θ(1/2) > 0`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangBKData

open _root_.StatMech _root_.StatMech.TwoDim _root_.StatMech.Lattice _root_.StatMech.Universality
open _root_.StatMech.Percolation Filter

-- At most one infinite cluster almost surely.
example : halfMeasure (atLeastTwoInfinite 2) = 0 := zbd_atLeastTwo_halfMeasure_zero

-- The two-scale merge error vanishes.
example := zbd_twoScaleError_tendsto_zero (zbd_centeredLeftSide 1) (zbd_centeredRightSide 1)

-- Merged side arms cross the box `[-1, 1] × [-2, 2]` horizontally.
example := zbd_centeredMerge_subset_horizontalCrossing 1 2 one_pos (by norm_num)

-- Conditional on percolation, boxes hit the infinite cluster with probability tending to `1`.
example (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto (fun n => halfMeasure.real (zbd_boxHitsInfinite n)) atTop (nhds 1) :=
  zbd_boxHitsInfinite_tendsto_one hpos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangBKData
