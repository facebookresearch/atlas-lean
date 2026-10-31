/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTorusCover

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTorusCover`

On the `3 × 3` torus:
* `torusReduceSite_add_period_x` at the origin;
* `torusPlanarPullback_injective`;
* `torusSquareHorizontalCrossing_period_false`: no configuration crosses a full period square;
* `bdcTorusThinCrossing_planarLift_subset_longRectangleUnion` at `alpha = n = 1`, and the thin
  cover structure `BdcTorusWindingToThinCover` is satisfiable (by the thin-crossing set itself),
  so `planarLift_subset_longRectangleUnion` applies.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTorusCover

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Lattice
open _root_.StatMech.RSW.Box _root_.StatMech.Universality

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- Reduction mod `3` is invariant under the horizontal period.
example (z : Site 2) : torusReduceSite 3 (z + ![(3 : ℤ), 0]) = torusReduceSite 3 z :=
  torusReduceSite_add_period_x 3 z

-- The planar pullback is injective.
example := torusPlanarPullback_injective 3

-- No configuration crosses a full period square horizontally.
example (omega : TorusAmbientConfig 3) : ¬ torusSquareHorizontalCrossing 3 3 omega :=
  torusSquareHorizontalCrossing_period_false 3 omega

-- Thin crossings lift into the long-rectangle union.
example := bdcTorusThinCrossing_planarLift_subset_longRectangleUnion 3 1 1

/-- The thin-crossing set is covered by thin crossings. -/
theorem thinCover : BdcTorusWindingToThinCover 3 1 1 {omega | bdcTorusThinCrossing 3 1 1 omega} :=
  ⟨fun _ h => h⟩

-- The conditional lift applies to a satisfiable cover.
example := thinCover.planarLift_subset_longRectangleUnion

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTorusCover
