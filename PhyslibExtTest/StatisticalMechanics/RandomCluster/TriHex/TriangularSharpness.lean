/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpness

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpness`

* `triangularOuterInnerTheta q β 0 = 1` (the degenerate radius);
* `triangularBoxGraph_edgeSet_nonempty` and `triangularOuterInnerDenom_pos` for the box of
  radius `1` at `q = 1`, `β = 1`;
* `triangular_outer_inner_differential_logistic` at `n = 1`, `q = 2`, `β = 1`;
* `triangularBox_differential_inequality` at `n = 1`, `q = 1`, `β = β₀ = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpness

open _root_.StatMech.FK.PeriodicPlanar

-- At radius `0` the crossing probability is `1` by convention.
example (q beta : ℝ) : triangularOuterInnerTheta q beta 0 = 1 := by
  simp [triangularOuterInnerTheta]

-- The box of radius `1` has an edge, and the OSSS denominator is positive there.
example : Nonempty (triangularBoxGraph 1).edgeSet :=
  triangularBoxGraph_edgeSet_nonempty 1 le_rfl

example : 0 < triangularOuterInnerDenom 1 1 1 :=
  triangularOuterInnerDenom_pos 1 le_rfl 1 1 le_rfl one_pos

-- The logistic differential inequality at a concrete parameter point.
example : triangularOuterInnerTheta 2 1 1 * (1 - triangularOuterInnerTheta 2 1 1) /
      triangularOuterInnerDenom 1 2 1 ≤ triangularOuterInnerThetaPrime 1 2 1 :=
  triangular_outer_inner_differential_logistic 1 le_rfl 2 1 (by norm_num) one_pos

-- The differential inequality for the wired crossing mass in the box of radius `1`.
example : ∃ c : ℝ, 0 < c ∧
    c * (triangularBoxCrossMass 1 1 1 / triangularBoxDenom 1 1 1) ≤
      deriv (triangularBoxCrossMass 1 1) 1 :=
  triangularBox_differential_inequality 1 le_rfl 1 1 1 le_rfl one_pos le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularSharpness
