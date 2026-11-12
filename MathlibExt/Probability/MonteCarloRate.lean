/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

/-!
# Sample mean: expectation and variance

For finitely many random variables with a common mean and a common variance, the sample
mean is unbiased and, under independence, its variance is `σ² / n`.

## i. Overview

Unbiasedness needs no independence: the integral of a finite sum is the sum of the integrals.
The variance computation needs independence: `IndepFun.variance_sum` turns the variance of
the sum into the sum of the variances, and the `(1 / n)²` factor from `variance_const_mul`
leaves `σ² / n`. Neither result needs a probability-measure hypothesis: the expectation
result uses only finite-sum integral linearity, and the variance result uses
`IndepFun.variance_sum`, which supplies the finiteness it needs from independence.

## ii. Key results

- `MathlibExt.Probability.integral_sample_mean`: the sample mean has expectation `mu`.
- `MathlibExt.Probability.variance_sample_mean`: the sample mean has variance `sigma2 / n`.
- `MathlibExt.Probability.variance_sample_mean_of_iid`: the IID case, derived from
  `variance_sample_mean` by specializing to `Fin n`.

## iii. Table of contents

- A. Expectation of the sample mean
- B. Variance of the sample mean
- C. The IID case

## iv. References

- `ProbabilityTheory.IndepFun.variance_sum` (Mathlib).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace MathlibExt.Probability

/-! ## A. Expectation of the sample mean -/

/-- The sample mean of finitely many random variables with a common mean
`mu` has expectation `mu` (no independence needed, and no probability-measure
hypothesis). -/
theorem integral_sample_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ι : Type*} [Fintype ι] [Nonempty ι]
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
variance `sigma2 / n`. Independence enters through `IndepFun.variance_sum`;
no probability-measure hypothesis is needed. -/
theorem variance_sample_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ} {sigma2 : ℝ}
    (hLp : ∀ i, MemLp (X i) 2 μ)
    (hIndep : iIndepFun (fun i => X i) μ)
    (hVar : ∀ i, variance (X i) μ = sigma2) :
    variance (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ)) μ
      = sigma2 / (Fintype.card ι : ℝ) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt hpos
  have hfun : (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ))
      = fun ω => (Fintype.card ι : ℝ)⁻¹ * (∑ i, X i) ω := by
    funext ω
    simp [div_eq_mul_inv, Finset.sum_apply, mul_comm]
  rw [hfun, variance_const_mul]
  have hsum : variance (∑ i, X i) μ = (Fintype.card ι : ℝ) * sigma2 := by
    rw [IndepFun.variance_sum (fun i _ => hLp i)
      (fun i _ j _ hij => hIndep.indepFun hij)]
    simp only [hVar, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum]
  field_simp

/-! ## C. The IID case -/

/-- For independent identically distributed square-integrable samples, the
variance of the sample mean is the single-sample variance divided by the
sample size. Square-integrability is required only of `X 0`; identical distribution transfers
it to every sample. This is `variance_sample_mean` specialized to `Fin n`. -/
theorem variance_sample_mean_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (n : ℕ) (hn : n ≠ 0) :
    variance (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) μ
      = variance (X 0) μ / (n : ℝ) := by
  let _ : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hgen := variance_sample_mean (ι := Fin n) (X := fun i : Fin n => X i.val)
    (sigma2 := variance (X 0) μ)
    (fun i => (hIdent i.val).memLp_iff.mpr hMemLp)
    (iIndepFun.precomp Fin.val_injective hIndep)
    (fun i => (hIdent i.val).variance_eq)
  rw [Fintype.card_fin] at hgen
  have hsum : (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
      = (fun ω => (∑ i : Fin n, X i.val ω) / (n : ℝ)) := by
    funext ω
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i => X i ω) n).symm
  rw [hsum]
  exact hgen

end MathlibExt.Probability
