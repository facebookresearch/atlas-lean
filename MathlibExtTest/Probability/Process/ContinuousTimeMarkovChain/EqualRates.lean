/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.EqualRates

/-! # Finite equal-rates chains -/

open ProbabilityTheory

/-- At time zero the whole transition matrix is the identity, not a uniform redraw. -/
example (μ : ℝ) : Matrix.of (equalRatesProb 3 μ 0) = 1 := by
  rw [equalRatesProb_eq_stickyKernel]
  simp [stickyKernel_one]

/-- At the saturation boundary the logarithm is totalized; distance no longer inverts time. -/
example : equalRatesDistance 3 (3 / 4) = 0 := by norm_num [equalRatesDistance]

/-- With just one possible jump, the off-diagonal entry is the entire mismatch probability. -/
example (μ t : ℝ) : equalRatesDistance 1 (equalRatesProb 1 μ t 0 1) = μ * t := by
  simp only [equalRatesDistance, equalRatesProb, Fin.zero_ne_one, ite_false]
  norm_num
  ring_nf
  rw [Real.log_exp]
  ring
