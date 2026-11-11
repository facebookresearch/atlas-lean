/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Sample mean: expectation and variance under IID sampling

For finitely many independent square-integrable random variables with
a common mean and a common variance, the sample mean is unbiased and
its variance is `σ² / n`.

## i. Overview

Unbiasedness needs no independence: the integral of a finite sum is
the sum of the integrals. The variance computation needs independence:
`variance` of the sum expands into a double sum of covariances
(`ProbabilityTheory.variance_sum`); the off-diagonal covariances vanish
for independent pairs (`IndepFun.covariance_eq_zero`), the diagonal
ones are the common variance, and the `(1 / n)²` factor from
`variance_const_mul` leaves `σ² / n`. Perfectly correlated samples
defeat the variance formula; degenerate variance `σ² = 0` gives `0`.

## ii. Key results

- `EarthScience.integral_sample_mean`: the sample mean has
  expectation `mu`.
- `EarthScience.variance_sample_mean`: the sample mean has variance
  `sigma2 / n`.

## iii. Table of contents

- A. Expectation of the sample mean
- B. Variance of the sample mean

## iv. References

- `ProbabilityTheory.variance_sum`,
  `ProbabilityTheory.IndepFun.covariance_eq_zero`,
  `ProbabilityTheory.covariance_self` (Mathlib).

## A. Expectation of the sample mean
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace EarthScience

/-- The sample mean of finitely many random variables with a common mean
`mu` has expectation `mu` (no independence needed). -/
theorem integral_sample_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ} {mu : ℝ}
    (hInt : ∀ i, Integrable (X i) μ) (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu) :
    ∫ ω, (∑ i, X i ω) / (Fintype.card ι : ℝ) ∂μ = mu := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt hpos
  have hfun : (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ))
      = fun ω => (Fintype.card ι : ℝ)⁻¹ * (∑ i, X i ω) := by
    funext ω
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun, integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hInt i)]
  simp only [hMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp


/-! ## B. Variance of the sample mean -/

/-- The sample mean of finitely many independent square-integrable
variables with common variance `sigma2` has
variance `sigma2 / n`. Independence enters through the vanishing
off-diagonal covariances. -/
theorem variance_sample_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ} {sigma2 : ℝ}
    (hLp : ∀ i, MemLp (X i) 2 μ)
    (hIndep : iIndepFun (fun i => X i) μ)
    (hVar : ∀ i, variance (X i) μ = sigma2) :
    variance (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ)) μ
      = sigma2 / (Fintype.card ι : ℝ) := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt hpos
  have hfun : (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ))
      = fun ω => (Fintype.card ι : ℝ)⁻¹ * (∑ i, X i) ω := by
    funext ω
    simp [div_eq_mul_inv, Finset.sum_apply, mul_comm]
  rw [hfun, variance_const_mul, variance_sum hLp]
  have hdiag : ∀ i, covariance (X i) (X i) μ = sigma2 := by
    intro i
    rw [covariance_self (hLp i).aestronglyMeasurable.aemeasurable, hVar i]
  have hinner : ∀ i, (∑ j, covariance (X i) (X j) μ) = sigma2 := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hoff : ∑ j ∈ Finset.univ.erase i, covariance (X i) (X j) μ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      exact IndepFun.covariance_eq_zero (hIndep.indepFun hij) (hLp i) (hLp j)
    rw [hdiag i, hoff, add_zero]
  simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end EarthScience
