/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance

/-!
# Variance of a sum of uncorrelated equal-variance period returns

If every period return has variance `σ²` and distinct periods are
uncorrelated (`cov = 0`), then the variance of the sum over all periods is
`(number of periods) * σ²`. Uncorrelatedness suffices: independence is not
assumed. In particular, annualized variance is `n * σ²` for `n` periods per
year.

## Main results

* `variance_sum_eq_card_mul_of_uncorrelated`: the variance-of-sum annualization.

Atlas roadmap target FI05.T05.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.VarianceAnnualization

set_option linter.unusedDecidableInType false in
/-- **Variance of a sum of uncorrelated equal-variance period returns.**
If every period return has variance `σ²` and distinct periods are uncorrelated
(`cov = 0`; independence is NOT assumed), then the variance of the sum over all
periods is `(number of periods) * σ²` (Atlas roadmap FI05.T05). In particular,
annualized variance is `n * σ²` for `n` periods per year. -/
theorem variance_sum_eq_card_mul_of_uncorrelated {ι : Type*} {Ω : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {R : ι → Ω → ℝ}
    (hR : ∀ i, MeasureTheory.MemLp (R i) 2 μ) {σ2 : ℝ}
    (hvar : ∀ i, ProbabilityTheory.variance (R i) μ = σ2)
    (huncorr : ∀ i j, i ≠ j → ProbabilityTheory.covariance (R i) (R j) μ = 0) :
    ProbabilityTheory.variance (fun ω => ∑ i, R i ω) μ = (Fintype.card ι : ℝ) * σ2 := by
  have hfun : (∑ i, R i) = fun ω => ∑ i, R i ω := by
    ext ω
    simp [Finset.sum_apply]
  rw [← hfun, ProbabilityTheory.variance_sum hR]
  have hinner : ∀ i, (∑ j, ProbabilityTheory.covariance (R i) (R j) μ) = σ2 := by
    intro i
    have h0 : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i →
        ProbabilityTheory.covariance (R i) (R j) μ = 0 :=
      fun j _ hji => huncorr i j (Ne.symm hji)
    have h1 : i ∉ (Finset.univ : Finset ι) →
        ProbabilityTheory.covariance (R i) (R i) μ = 0 :=
      fun hi => absurd (Finset.mem_univ i) hi
    rw [Finset.sum_eq_single i h0 h1,
      ProbabilityTheory.covariance_self (hR i).aemeasurable, hvar i]
  simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end MathlibExt.Probability.Finance.VarianceAnnualization
