/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.EqualRates

/-! # The two-state equal-rates chain -/

open ProbabilityTheory

/-- With just one possible jump, the off-diagonal entry is the entire mismatch probability. -/
example (μ t : ℝ) : equalRatesDistance 1 (equalRatesProb 1 μ t 0 1) = μ * t := by
  simp only [equalRatesDistance, equalRatesProb, Fin.zero_ne_one, ite_false]
  norm_num
  ring_nf
  rw [Real.log_exp]
  ring
