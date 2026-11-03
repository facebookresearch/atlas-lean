/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossingCounterexample

/-!
# Tests for
`PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossingCounterexample`

On the `3 × 3` torus:
* the explicit configuration `torusSquareShiftCounterexampleConfig 3` has both a horizontal
  unit-square crossing and a dual vertical crossing;
* `torus_concreteSquareCrossing_duality_iff_false`: the exact duality hypothesis is refuted;
* `torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover` at `q = 1`, `n = 1`, in
  conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
namespace TorusSquareCrossingCounterexample

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The counterexample configuration crosses the unit square horizontally.
example := torusSquareShiftCounterexample_horizontal 3

-- Its dual crosses the unit square vertically.
example := torusSquareShiftCounterexample_dual_vertical 3

-- The exact square-crossing duality fails on the `3 × 3` torus.
example : ¬ ∀ omega : TorusAmbientConfig 3,
    ¬ torusSquareHorizontalCrossing 3 1 omega ↔
      torusCellDualAmbientConfig 3 omega ∈ torusSquareVerticalCrossingEvent 3 1 :=
  torus_concreteSquareCrossing_duality_iff_false 3

-- The `1 / (1 + q)` bound at `q = 1` from a one-sided cover.
example (hcover : ∀ omega : TorusAmbientConfig 3,
      ¬ torusSquareHorizontalCrossing 3 1 omega →
        torusCellDualAmbientConfig 3 omega ∈ torusSquareVerticalCrossingEvent 3 1) :
    1 / (1 + 1 : ℝ) ≤ torusAmbientEventProbability 3 (selfDualPoint 1) 1
      (torusSquareHorizontalCrossingEvent 3 1) :=
  torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover 3 1 le_rfl (by norm_num) le_rfl
    hcover

end TorusSquareCrossingCounterexample
end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
