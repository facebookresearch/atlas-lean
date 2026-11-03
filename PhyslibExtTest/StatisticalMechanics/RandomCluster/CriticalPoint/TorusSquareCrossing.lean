/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossing`

On the `3 × 3` torus:
* `torusAmbientEventProbability_rotated` for the horizontal unit-square crossing event;
* `torusAmbientDualPullbackEventProbability_le` at `q = 2`;
* `torus_squareCrossing_const_pos` at `q = 2`;
* `torus_concreteSquareCrossing_ge_one_div_one_add_q` stated in conditional form only: its
  hypothesis is refuted at `n = 1` (`TorusSquareCrossingCounterexample`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossing

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- Rotation invariance of the torus measure.
example := torusAmbientEventProbability_rotated 3 (1 / 2) 2 (torusSquareHorizontalCrossingEvent 3 1)

-- Dual pullback costs at most a factor `q`.
example := torusAmbientDualPullbackEventProbability_le 3 (torusSquareHorizontalCrossingEvent 3 1)
  (q := 2) (by norm_num)

-- The lower-bound constant is positive.
example : 0 < 1 / (1 + (2 : ℝ)) := torus_squareCrossing_const_pos (by norm_num)

-- Conditional form (the hypothesis is false at `n = 1`).
example (h : ∀ omega : TorusAmbientConfig 3, ¬ torusSquareHorizontalCrossing 3 1 omega ↔
      torusCellDualAmbientConfig 3 omega ∈ torusSquareVerticalCrossingEvent 3 1) :
    1 / (1 + 1 : ℝ) ≤ torusAmbientEventProbability 3 (selfDualPoint 1) 1
      (torusSquareHorizontalCrossingEvent 3 1) :=
  torus_concreteSquareCrossing_ge_one_div_one_add_q 3 1 le_rfl (by norm_num) le_rfl h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossing
