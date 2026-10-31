/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTorusPushforward

/-!
# Tests for
`PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTorusPushforward`

On the `3 × 3` torus at `p = 1/2`, `q = 2`:
* `torusAmbientMeasure_positivelyAssociated` (FKG) and the probability-measure instance;
* `torusPlanarPushforward_allShiftInvariant`;
* `bdcLongRectangle_polynomial_deficit_of_torusCover` fully instantiated: the thin cover is the
  thin-crossing set itself and `c = 1`, `ε = 0` makes the winding hypothesis trivial.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
namespace LongRectangleTorusPushforward

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Lattice _root_.StatMech.Onsager
open _root_.StatMech.Universality MeasureTheory

instance : Fact (2 < 3) := ⟨by norm_num⟩

/-- `1/2` is positive. -/
theorem hp : (0 : ℝ) < 1 / 2 := by norm_num

/-- `1/2` is below `1`. -/
theorem hp1 : (1 / 2 : ℝ) < 1 := by norm_num

/-- `2` is positive. -/
theorem hq : (0 : ℝ) < 2 := by norm_num

-- The torus random-cluster measure is a probability measure.
example : IsProbabilityMeasure (torusAmbientMeasure 3 hp hp1 hq) := inferInstance

-- FKG for the torus measure at `q = 2`.
example : PositivelyAssociated (torusAmbientMeasure 3 hp hp1 hq) :=
  torusAmbientMeasure_positivelyAssociated 3 hp hp1 hq (by norm_num)

-- The planar pushforward is translation invariant.
example := torusPlanarPushforward_allShiftInvariant 3 hp hp1 hq

-- The long-rectangle deficit bound for the pushforward, with all hypotheses discharged.
example := bdcLongRectangle_polynomial_deficit_of_torusCover 3 hp hp1 hq (by norm_num)
  (alpha := 1) (n := 1) one_pos le_rfl {omega | bdcTorusThinCrossing 3 1 1 omega}
  ⟨fun _ h => h⟩ (c := 1) (epsilon := 0) zero_le_one (by simp)

end LongRectangleTorusPushforward
end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
