/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LeftFillInteriorArc

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LeftFillInteriorArc`

* `crr_square_half` at `n = 2` with every measurability hypothesis discharged: `1/2 ≤ P(horizontal
  crossing of [0, 2]²)` unconditionally;
* the hypothesis `¬ HorizontalCrossing` of the combinatorial lemmas is satisfiable: the all-closed
  configuration has no horizontal crossing of `[0, 1]²`;
* `crr_leftFillFrameArcOrder` and `crr_interfaceCoastConnected` for that configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LeftFillInteriorArc

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.RSW.Box _root_.StatMech.Universality

-- The square-crossing bound at `p = 1/2`, unconditionally.
example : (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent 0 2 0 2) :=
  crr_square_half 2 (by norm_num) (measurableSet_horizontalCrossingEvent _ _ _ _)
    (measurableSet_verticalCrossingEvent _ _ _ _) (measurableSet_horizontalCrossingEvent _ _ _ _)

/-- The all-closed configuration does not cross `[0, 1]²` horizontally. -/
theorem closed_noH : ¬ HorizontalCrossing (fun _ => false) 0 1 0 1 := by
  rintro ⟨x, y, h⟩
  have hbot : openSubgraphInduce 2 (fun _ => false) (rect 0 1 0 1) = ⊥ := by
    ext a b
    simp [openSubgraphInduce]
  unfold ConnectedWithin at h
  rw [hbot, SimpleGraph.reachable_bot] at h
  have := congrArg (fun z : rect 0 1 0 1 => (z : Site 2) 0) h
  have hx := x.2.2
  have hy := y.2.2
  simp only at this
  omega

-- The frame-arc order holds for the all-closed configuration.
example := crr_leftFillFrameArcOrder (fun _ => false) 1 closed_noH

-- The interface coast is connected for the all-closed configuration.
example := crr_interfaceCoastConnected (fun _ => false) 1 closed_noH

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LeftFillInteriorArc
