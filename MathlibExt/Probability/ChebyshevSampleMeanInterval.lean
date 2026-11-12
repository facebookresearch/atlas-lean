/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MonteCarloRate
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic

/-!
# Chebyshev confidence interval for the sample mean

For independent square-integrable samples with a common mean `mu` and a
common variance `σ ^ 2`, the interval `mean ± k * σ / √n` fails to cover
`mu` with probability at most `1 / k ^ 2`.

## i. Overview

The non-coverage set is contained in the deviation set
`{ω | k * σ / √n ≤ |mean ω - mu|}`. The sample mean has expectation `mu`
(`integral_sample_mean`) and variance `σ ^ 2 / n`
(`variance_sample_mean`). Chebyshev's inequality
(`meas_ge_le_variance_div_sq`) then bounds the deviation probability by
`(σ ^ 2 / n) / (k * σ / √n) ^ 2 = 1 / k ^ 2`.

## ii. Key results

- `MathlibExt.Probability.chebyshev_sample_mean_interval_failure_bound`:
  the Chebyshev interval for the sample mean has failure probability at
  most `1 / k ^ 2`.

## iii. References

- `ProbabilityTheory.meas_ge_le_variance_div_sq` (Chebyshev's inequality,
  Mathlib).
- `ProbabilityTheory.IndepFun.variance_sum` (Mathlib).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability

/-- Chebyshev confidence interval for the sample mean: the interval
`mean ± k * σ / √n` fails to cover the true mean `mu` with probability at most
`1 / k ^ 2`, for independent square-integrable samples with common mean `mu`
and common variance `σ ^ 2`. -/
theorem chebyshev_sample_mean_interval_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    {X : Fin n → Ω → ℝ} {mu sigma : ℝ} (hsigma : 0 < sigma)
    (hLp : ∀ i, MemLp (X i) 2 μ) (hIndep : iIndepFun X μ)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu)
    (hVar : ∀ i, variance (X i) μ = sigma ^ 2) {k : ℝ} (hk : 0 < k) :
    μ {ω | mu ∉ Set.Icc ((∑ i, X i ω) / (n : ℝ) - k * sigma / Real.sqrt (n : ℝ))
      ((∑ i, X i ω) / (n : ℝ) + k * sigma / Real.sqrt (n : ℝ))}
      ≤ ENNReal.ofReal (1 / k ^ 2) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  have hc : 0 < k * sigma / Real.sqrt (n : ℝ) :=
    div_pos (mul_pos hk hsigma) hsqrt_pos
  have hInt : ∀ i, Integrable (X i) μ := fun i => (hLp i).integrable one_le_two
  have hS_mem : MemLp (fun ω => ∑ i, X i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hLp i)
  have hM_eq : (fun ω => (∑ i, X i ω) / (n : ℝ)) = fun ω => (n : ℝ)⁻¹ * (∑ i, X i ω) := by
    funext ω
    exact div_eq_inv_mul _ _
  have hM_mem : MemLp (fun ω => (∑ i, X i ω) / (n : ℝ)) 2 μ := by
    rw [hM_eq]
    exact hS_mem.const_mul _
  have hM_int : ∫ ω, (∑ i, X i ω) / (n : ℝ) ∂μ = mu := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    have h := integral_sample_mean (ι := Fin n) (X := X) (mu := mu) hInt hMean
    rwa [Fintype.card_fin] at h
  have hM_var : variance (fun ω => (∑ i, X i ω) / (n : ℝ)) μ
      = sigma ^ 2 / (n : ℝ) := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    have h := variance_sample_mean (ι := Fin n) (X := X) (sigma2 := sigma ^ 2)
      hLp hIndep hVar
    rwa [Fintype.card_fin] at h
  have hsub : {ω | mu ∉ Set.Icc ((∑ i, X i ω) / (n : ℝ) - k * sigma / Real.sqrt (n : ℝ))
        ((∑ i, X i ω) / (n : ℝ) + k * sigma / Real.sqrt (n : ℝ))}
      ⊆ {ω | k * sigma / Real.sqrt (n : ℝ) ≤ |(∑ i, X i ω) / (n : ℝ) - mu|} := by
    intro ω h
    simp only [Set.mem_ofPred_eq] at h ⊢
    by_contra hcon
    rw [not_le] at hcon
    rw [abs_lt] at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply h
    rw [Set.mem_Icc]
    constructor <;> linarith
  have hcheb : μ {ω | k * sigma / Real.sqrt (n : ℝ) ≤ |(∑ i, X i ω) / (n : ℝ) - mu|}
      ≤ ENNReal.ofReal (sigma ^ 2 / (n : ℝ) / (k * sigma / Real.sqrt (n : ℝ)) ^ 2) := by
    have h := meas_ge_le_variance_div_sq hM_mem hc
    rw [hM_int, hM_var] at h
    exact h
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have hcalc : sigma ^ 2 / (n : ℝ) / (k * sigma / Real.sqrt (n : ℝ)) ^ 2
      = 1 / k ^ 2 := by
    rw [div_pow, mul_pow, hsq]
    field_simp [hn', hk_ne, hsigma_ne]
  rw [hcalc] at hcheb
  exact le_trans (measure_mono hsub) hcheb

end MathlibExt.Probability
