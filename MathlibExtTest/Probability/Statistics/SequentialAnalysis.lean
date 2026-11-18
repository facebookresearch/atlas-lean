/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SequentialAnalysis

/-!
# Tests for the objects of sequential analysis

The CUSUM closed form at `n = 1` is Page's first step `max (log L(X₁)) 0`, and the CUSUM
statistic is nonnegative.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExtTest.Probability.Statistics.SequentialAnalysis

variable {X : Type*} [MeasurableSpace X] (P₀ P₁ : Measure X) (ω : ℕ → X)

/-- First CUSUM step from the closed form. -/
example : pageCusum P₀ P₁ 1 ω = max (llr P₁ P₀ (ω 0)) 0 := by
  rw [pageCusum_eq_sup]
  simp [Finset.sup'_insert, Finset.range_add_one]
  rw [max_comm]

/-- The CUSUM statistic is nonnegative: the empty final segment contributes `0`. -/
theorem pageCusum_nonneg (n : ℕ) : 0 ≤ pageCusum P₀ P₁ n ω := by
  rw [pageCusum_eq_sup]
  exact Finset.le_sup'_of_le _ (b := n) (by simp) (by simp)

/-- The cumulative log-likelihood ratio is additive in the observations. -/
example (n : ℕ) :
    llrSum P₀ P₁ (n + 1) ω = llrSum P₀ P₁ n ω + llr P₁ P₀ (ω n) := by
  simp [llrSum, Finset.sum_range_succ]

end MathlibExtTest.Probability.Statistics.SequentialAnalysis
