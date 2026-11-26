/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossingCover

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossingCover`

On the `3 × 3` torus:
* `torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional` at `n = 1`, `q = 1` and
  `n = 2`, `q = 4` (no hypotheses);
* `torus_concreteSquareCrossing_dual_cover` at `n = 1` (one-sided cover);
* `torusReduceSite` of `(4, -1)` is `(1, 2)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossingCover

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Lattice _root_.StatMech.Onsager
open _root_.StatMech.RSW.Box _root_.StatMech.Universality

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- Square crossing at `p_sd(1) = 1/2` has probability at least `1/2`.
example : 1 / (1 + 1 : ℝ) ≤ torusAmbientEventProbability 3 (selfDualPoint 1) 1
    (torusSquareHorizontalCrossingEvent 3 1) :=
  torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional 3 1 le_rfl (by norm_num) le_rfl

-- The `2 × 2` square at `q = 4`.
example : 1 / (1 + 4 : ℝ) ≤ torusAmbientEventProbability 3 (selfDualPoint 4) 4
    (torusSquareHorizontalCrossingEvent 3 2) :=
  torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional 3 2 (by norm_num) (by norm_num)
    (by norm_num)

-- No horizontal crossing forces a dual vertical crossing.
example (omega : TorusAmbientConfig 3) (h : ¬ torusSquareHorizontalCrossing 3 1 omega) :
    torusCellDualAmbientConfig 3 omega ∈ torusSquareVerticalCrossingEvent 3 1 :=
  torus_concreteSquareCrossing_dual_cover 3 1 le_rfl (by norm_num) omega h

-- Reduction of a site mod `3`.
example : torusReduceSite 3 ![4, -1] = (1, 2) := by decide

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusSquareCrossingCover
