/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.HoeffdingBounded

open MeasureTheory ProbabilityTheory Real

namespace MathlibExt.Probability.HoeffdingBounded

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

-- Bach's Proposition 1.2: variables in `[0, 1]` give the exponent `-2 n t²`.
example {n : ℕ} {Z : Fin n → Ω → ℝ} (h_indep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ) (hZ : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]} ≤
      exp (-2 * n * t ^ 2) := by
  simpa using measureReal_avg_sub_ge_le h_indep hmeas hZ ht

-- Bach's Corollary 1.1: the two-sided bound for variables in `[0, 1]`.
example {n : ℕ} {Z : Fin n → Ω → ℝ} (h_indep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ) (hZ : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]|} ≤
      2 * exp (-2 * n * t ^ 2) := by
  simpa using measureReal_abs_avg_sub_ge_le h_indep hmeas hZ ht

end MathlibExt.Probability.HoeffdingBounded
