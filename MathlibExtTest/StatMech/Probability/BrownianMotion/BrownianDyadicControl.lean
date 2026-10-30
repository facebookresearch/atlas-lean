/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianDyadicControl
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianDyadicControl`

* The grid data at small inputs: `brownianDyadicDenominator 1 = 256`,
  `brownianDyadicPoint 1 1 128 = -1/2`, `brownianDyadicThreshold 1 = 1/2`.
* `brownianProductLaw_brownianDyadicBadEvent_le` at `N = 1`, `n = 2`, and the Borel–Cantelli
  conclusion `brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianDyadicControl

example : brownianDyadicDenominator 1 = 256 := by simp [brownianDyadicDenominator]

example : brownianDyadicPoint 1 1 128 = -1 / 2 := by
  simp [brownianDyadicPoint, brownianDyadicDenominator]; norm_num

example : brownianDyadicThreshold 1 = 2⁻¹ := by simp [brownianDyadicThreshold]

example : brownianProductLaw (brownianDyadicBadEvent 1 2) ≤ ((6 * 1 : ℕ) : ℝ≥0∞) * (16⁻¹) ^ 2 :=
  brownianProductLaw_brownianDyadicBadEvent_le 1 2

example : ∀ᵐ ω ∂brownianProductLaw, ∀ N : ℕ, ∀ᶠ n in Filter.atTop,
    ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
      edist (brownianCoordinateProcess (brownianDyadicPoint N n k) ω)
        (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) ω) <
          brownianDyadicThreshold n :=
  brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianDyadicControl
