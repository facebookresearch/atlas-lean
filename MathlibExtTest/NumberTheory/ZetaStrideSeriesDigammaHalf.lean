/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZetaStrideSeriesDigammaHalf

/-! # Tests for the half-shift digamma series -/

open Filter MetaMathlibExt Topology

-- The smallest stride and exponent are both allowed.
example :
    Tendsto (fun N : ℕ ↦ (↑(∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + 1) / (((n : ℝ) + 1 + 1 / 2) * ((n : ℝ) + 1 - 1 / 2 + 1)) *
          strideAlternatingSum 1 1 (n + 1)) : ℂ)) atTop
      (𝓝 ((∑' n : ℕ, 1 / ((n : ℂ) + 1) *
          (Complex.digamma (((n : ℂ) + 1 + 1 / 2 + 1) / 2) -
            Complex.digamma (((n : ℂ) + 1 + 1 / 2) / 2))) / 2 +
        (∑' n : ℕ, 1 / ((n : ℂ) + 1) *
          (Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 2) / 2) -
            Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 1) / 2))) / 2)) := by
  simpa only [Nat.cast_one, pow_one, mul_one] using
    tendsto_strideAlternatingSum_digamma_half 1 1 (by decide) (by decide)

-- Stride two at exponent one exercises both residue classes at the convergence boundary.
example :
    Tendsto (fun N : ℕ ↦ (↑(∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + 2) / (((n : ℝ) + 1 + 1 / 2) * ((n : ℝ) + 1 - 1 / 2 + 2)) *
          strideAlternatingSum 2 1 (n + 1)) : ℂ)) atTop
      (𝓝 ((∑' n : ℕ, 1 / ((n : ℂ) + 1) *
          (Complex.digamma (((n : ℂ) + 1 + 1 / 2 + 2) / (2 * 2)) -
            Complex.digamma (((n : ℂ) + 1 + 1 / 2) / (2 * 2)))) / (2 * 2) +
        (∑' n : ℕ, 1 / ((n : ℂ) + 1) *
          (Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 2 * 2) / (2 * 2)) -
            Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 2) / (2 * 2)))) / (2 * 2))) := by
  simpa only [Nat.cast_ofNat, pow_one] using
    tendsto_strideAlternatingSum_digamma_half 2 1 (by decide) (by decide)
