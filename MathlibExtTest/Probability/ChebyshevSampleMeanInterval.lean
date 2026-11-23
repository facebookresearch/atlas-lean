/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ChebyshevSampleMeanInterval

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Concrete non-vacuous case: `n = 2`, `σ = 1`, `k = 2`. The Chebyshev
interval `mean ± 2 / √2` fails to cover `mu` with probability at most
`1 / 4`, a bound strictly below `1`, so the theorem is not vacuous. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin 2 → Ω → ℝ} {mu : ℝ}
    (hLp : ∀ i, MemLp (X i) 2 μ) (hIndep : iIndepFun X μ)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu)
    (hVar : ∀ i, variance (X i) μ = (1 : ℝ) ^ 2) :
    μ {ω | mu ∉ Set.Icc ((∑ i, X i ω) / (2 : ℝ) - 2 * 1 / Real.sqrt (2 : ℝ))
      ((∑ i, X i ω) / (2 : ℝ) + 2 * 1 / Real.sqrt (2 : ℝ))}
      ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have h := MathlibExt.Probability.chebyshev_sample_mean_interval_failure_bound
    (n := 2) (two_ne_zero) (X := X) (mu := mu) (sigma := 1) one_pos hLp hIndep
    hMean hVar (k := 2) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Boundary case `k = 1`: the failure bound is `1`, i.e. the trivial bound.
The theorem still applies and the interval is `mean ± σ / √n`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin 4 → Ω → ℝ} {mu : ℝ}
    (hLp : ∀ i, MemLp (X i) 2 μ) (hIndep : iIndepFun X μ)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu)
    (hVar : ∀ i, variance (X i) μ = (2 : ℝ) ^ 2) :
    μ {ω | mu ∉ Set.Icc ((∑ i, X i ω) / (4 : ℝ) - 1 * 2 / Real.sqrt (4 : ℝ))
      ((∑ i, X i ω) / (4 : ℝ) + 1 * 2 / Real.sqrt (4 : ℝ))}
      ≤ ENNReal.ofReal (1 : ℝ) := by
  have h := MathlibExt.Probability.chebyshev_sample_mean_interval_failure_bound
    (n := 4) (by norm_num) (X := X) (mu := mu) (sigma := 2) (by norm_num) hLp hIndep
    hMean hVar (k := 1) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The half-width formula at concrete values: for `n = 4`, `σ = 2`, `k = 2`,
the half-width `k * σ / √n` is exactly `2`. -/
example : (2 : ℝ) * 2 / Real.sqrt (4 : ℝ) = 2 := by
  rw [show Real.sqrt (4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  norm_num
