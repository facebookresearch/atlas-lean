/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.Landau

import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Tests for Landau's theorem on Dirichlet series with nonnegative coefficients

The hypotheses are met by `a n = 1`, whose abscissa of absolute convergence is `1`: Landau's
theorem then says `∑ n⁻ˢ` does not continue holomorphically across `s = 1`.
-/

@[expose] public section

namespace LandauTest

/-- `∑ n⁻ˢ` has a singularity at `s = 1`. -/
example : ¬ ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball ((1 : ℝ) : ℂ) r) ∧
    Set.EqOn g (LSeries fun _ : ℕ => ((1 : ℝ) : ℂ))
      (Metric.ball ((1 : ℝ) : ℂ) r ∩ {z : ℂ | (1 : ℝ) < z.re}) := by
  refine LSeries.not_exists_holomorphic_extension_of_nonneg (fun _ => 1) (fun _ => zero_le_one) ?_
  have : (fun _ : ℕ => ((1 : ℝ) : ℂ)) = 1 := by funext _; simp
  rw [this, LSeries.abscissaOfAbsConv_one]
  rfl

end LandauTest
