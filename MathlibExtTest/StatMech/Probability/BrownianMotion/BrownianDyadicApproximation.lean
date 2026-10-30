/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianDyadicApproximation
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianDyadicApproximation`

* `brownianDyadicApproxIndex` and `brownianDyadicApproxPoint` at small inputs: for `N = 1`,
  `n = 0`, the point `t = 1/2` has index `1` and approximating grid point `0`.
* `dist_brownianDyadicApproxPoint_lt_mesh` at `t = 1/2`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianDyadicApproximation

example : brownianDyadicApproxIndex 1 0 (1 / 2) = 1 := by
  simp [brownianDyadicApproxIndex, brownianDyadicDenominator]
  norm_num [Nat.floor_eq_iff]

example : brownianDyadicApproxPoint 1 0 (1 / 2) = 0 := by
  have : brownianDyadicApproxIndex 1 0 (1 / 2) = 1 := by
    simp [brownianDyadicApproxIndex, brownianDyadicDenominator]
    norm_num [Nat.floor_eq_iff]
  rw [brownianDyadicApproxPoint, this]
  simp [brownianDyadicPoint, brownianDyadicDenominator]

example : dist (brownianDyadicApproxPoint 1 0 (1 / 2)) (1 / 2) <
    ((brownianDyadicDenominator 0 : ℕ) : ℝ)⁻¹ :=
  dist_brownianDyadicApproxPoint_lt_mesh 1 0 (by norm_num)

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianDyadicApproximation
