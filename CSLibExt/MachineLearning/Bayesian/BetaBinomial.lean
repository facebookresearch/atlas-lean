/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.Basic
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Binomial

/-!
# The beta-binomial model

The success probability `θ` of a coin has a `Beta(a, b)` prior (Mathlib's `betaMeasure a b`) and the
data are the number of successes in `n` flips, `Bin(n, θ)` (`binomialKernel n`, built on Mathlib's
`binomial`). A single flip is the Bernoulli case `n = 1`. The count is a sufficient statistic for a
sequence of flips, so the results below also describe Bernoulli sequences.

* `betaPDFReal_mul_pow`: the `Beta(a, b)` density times `θ ^ k (1 - θ) ^ m` is
  `B(a + k, b + m) / B(a, b)` times the `Beta(a + k, b + m)` density. This is the computation
  behind conjugacy.
* `binomialKernel_comp_betaMeasure` (**beta-binomial distribution**): the evidence of `k`
  successes is `C(n, k) B(a + k, b + n - k) / B(a, b)`.
* `posterior_binomialKernel_betaMeasure` (**conjugacy**): after `k` successes in `n` trials, the
  posterior is `Beta(a + k, b + n - k)`. The posterior is Mathlib's `κ†μ`, identified through Bayes'
  rule for discrete observations (`posterior_eq_bayesPosterior`).
* `binomialKernel_one_comp_betaMeasure`: the prior predictive probability of a success is the prior
  mean `a / (a + b)`, via `beta_add_one_left`.
* `posterior_predictive_betaMeasure` (**posterior predictive**): after `k` successes in `n`
  trials, the next trial succeeds with probability `(a + k) / (a + b + n)`. For the uniform prior
  `a = b = 1` this is Laplace's rule of succession, `(k + 1) / (n + 2)`.

The maximum-likelihood estimate `k / n` of the same model is Casella–Berger, Example 7.2.7, in
`FormalizedTextbooks/CasellaBergerStatisticalInference/Chapter7/BernoulliEstimation.lean`.

## References

* K. P. Murphy, *Probabilistic Machine Learning: An Introduction*, MIT Press, 2022, Chapter 4
  (the beta-binomial model).
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §2.1.1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Bayesian

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

/-- **Binomial likelihood kernel.** For a natural number $n$, the binomial kernel sends a real
$\theta$ to the binomial distribution $\mathrm{Bin}(n, p)$ on $\mathbb{N}$, the law of the number of
successes in $n$ independent coin flips with success probability $p$, where $p$ is $\theta$
clipped to $[0, 1]$. -/
noncomputable def binomialKernel (n : ℕ) : Kernel ℝ ℕ where
  toFun θ := binomial n (projIcc 0 1 zero_le_one θ)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp_rw [← Measure.tsum_indicator_apply_singleton _ s hs]
    refine Measurable.tsum fun k ↦ ?_
    by_cases hk : k ∈ s
    · simp only [Set.indicator_of_mem hk, binomial_singleton]
      refine ENNReal.measurable_ofReal.comp ?_
      fun_prop
    · simp only [Set.indicator_of_notMem hk]
      exact measurable_const

instance (n : ℕ) : IsMarkovKernel (binomialKernel n) :=
  ⟨fun _ ↦ isProbabilityMeasure_binomial⟩

theorem binomialKernel_apply_singleton (n k : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    binomialKernel n θ {k} = ENNReal.ofReal (n.choose k * θ ^ k * (1 - θ) ^ (n - k)) := by
  change binomial n _ {k} = _
  rw [binomial_singleton, projIcc_of_mem _ ⟨h0, h1⟩]

/-! ### Beta integrals -/

section Beta

/-- **Recurrence for the beta function in the first argument.** For real $a > 0$ and $b > 0$, the
beta function $B(a, b) = \Gamma(a)\Gamma(b)/\Gamma(a + b)$ satisfies
$B(a + 1, b) = B(a, b) \cdot \frac{a}{a + b}$. -/
theorem beta_add_one_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    beta (a + 1) b = beta a b * (a / (a + b)) := by
  have hab : (0 : ℝ) < a + b := add_pos ha hb
  simp only [beta]
  rw [Real.Gamma_add_one ha.ne', show a + 1 + b = (a + b) + 1 by ring,
    Real.Gamma_add_one hab.ne']
  have h1 := Real.Gamma_pos_of_pos hab
  field_simp

theorem betaPDFReal_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (θ : ℝ) :
    0 ≤ betaPDFReal a b θ := by
  unfold betaPDFReal
  split_ifs with h
  · have := beta_pos ha hb
    have := Real.rpow_nonneg h.1.le (a - 1)
    have := Real.rpow_nonneg (sub_pos.mpr h.2).le (b - 1)
    positivity
  · exact le_rfl

/-- **Conjugacy of the beta density.** Let $a, b > 0$ be real, $k, m$ natural numbers and
$\theta$ real. Write $f_{a,b}$ for the $\mathrm{Beta}(a, b)$ density (zero outside $(0, 1)$) and
$B(a, b) = \Gamma(a)\Gamma(b)/\Gamma(a + b)$ for the beta function. Then
$f_{a,b}(\theta) \, \theta^k (1 - \theta)^m =
\frac{B(a + k, b + m)}{B(a, b)} f_{a + k, b + m}(\theta)$. -/
theorem betaPDFReal_mul_pow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k m : ℕ) (θ : ℝ) :
    betaPDFReal a b θ * (θ ^ k * (1 - θ) ^ m) =
      beta (a + k) (b + m) / beta a b * betaPDFReal (a + k) (b + m) θ := by
  have hB := (beta_pos ha hb).ne'
  have hB' := (beta_pos (α := a + k) (β := b + m) (by positivity) (by positivity)).ne'
  unfold betaPDFReal
  split_ifs with h
  · have h0 := h.1
    have h1 : 0 < 1 - θ := sub_pos.mpr h.2
    rw [show a + k - 1 = (a - 1) + (k : ℝ) by ring, show b + m - 1 = (b - 1) + (m : ℝ) by ring,
      Real.rpow_add h0, Real.rpow_add h1, Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  · simp

end Beta

/-! ### The beta-binomial model -/

section Conjugacy

variable {a b : ℝ}

/-- **Beta prior times binomial likelihood.** Let $a, b > 0$ be real, $n, k$ natural numbers,
$m = n - k$ if $k \le n$ and $m = 0$ otherwise, and $\theta$ real. Write $f_{a,b}$ for the
$\mathrm{Beta}(a, b)$ density (zero outside $(0, 1)$) and $B$ for the beta function. Then the
density $f_{a,b}(\theta)$ times the probability that the binomial kernel at $\theta$ gives exactly
$k$ successes in $n$ trials equals
$\binom{n}{k} \frac{B(a + k, b + m)}{B(a, b)} f_{a + k, b + m}(\theta)$, as an identity in
$[0, \infty]$. -/
theorem betaPDF_mul_binomialKernel (ha : 0 < a) (hb : 0 < b) {n k : ℕ} (θ : ℝ) :
    betaPDF a b θ * binomialKernel n θ {k} =
      ENNReal.ofReal (n.choose k * (beta (a + k) (b + (n - k : ℕ)) / beta a b)) *
        betaPDF (a + k) (b + (n - k : ℕ)) θ := by
  by_cases h : 0 < θ ∧ θ < 1
  · rw [binomialKernel_apply_singleton n k h.1.le h.2.le, betaPDF, betaPDF,
      ← ENNReal.ofReal_mul (betaPDFReal_nonneg ha hb θ), ← ENNReal.ofReal_mul (by
        have := beta_pos ha hb
        have := beta_pos (α := a + k) (β := b + (n - k : ℕ)) (by positivity) (by positivity)
        positivity)]
    congr 1
    rw [show n.choose k * θ ^ k * (1 - θ) ^ (n - k) =
      n.choose k * (θ ^ k * (1 - θ) ^ (n - k)) by ring, mul_left_comm,
      betaPDFReal_mul_pow ha hb k (n - k) θ]
    ring
  · rcases not_and_or.mp h with h | h
    · rw [betaPDF_eq_zero_of_nonpos (not_lt.mp h), betaPDF_eq_zero_of_nonpos (not_lt.mp h)]
      simp
    · rw [betaPDF_eq_zero_of_one_le (not_lt.mp h), betaPDF_eq_zero_of_one_le (not_lt.mp h)]
      simp

theorem withDensity_binomialKernel (ha : 0 < a) (hb : 0 < b) (n k : ℕ) :
    ((betaMeasure a b).withDensity fun θ ↦ binomialKernel n θ {k}) =
      ENNReal.ofReal (n.choose k * (beta (a + k) (b + (n - k : ℕ)) / beta a b)) •
        betaMeasure (a + k) (b + (n - k : ℕ)) := by
  have hpdf : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  rw [betaMeasure, ← withDensity_mul _ hpdf
    ((binomialKernel n).measurable_coe (measurableSet_singleton k)), betaMeasure,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext θ
  exact betaPDF_mul_binomialKernel ha hb θ

/-- **The beta-binomial distribution.** Let $a, b > 0$ be real, $n, k$ natural numbers and
$B(x, y) = \Gamma(x)\Gamma(y)/\Gamma(x + y)$ the beta function. Under a $\mathrm{Beta}(a, b)$
prior on the success probability, the marginal probability (the evidence) that the binomial kernel
gives exactly $k$ successes in $n$ trials is $\binom{n}{k} \frac{B(a + k, b + n - k)}{B(a, b)}$,
where $n - k$ is truncated at $0$. -/
theorem binomialKernel_comp_betaMeasure (ha : 0 < a) (hb : 0 < b) {n k : ℕ} :
    (binomialKernel n ∘ₘ betaMeasure a b) {k} =
      ENNReal.ofReal (n.choose k * (beta (a + k) (b + (n - k : ℕ)) / beta a b)) := by
  have := isProbabilityMeasureBeta (α := a + k) (β := b + (n - k : ℕ)) (by positivity)
    (by positivity)
  rw [← withDensity_univ_eq_comp, withDensity_binomialKernel ha hb, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]

/-- **Beta–binomial conjugacy.** Let $a, b > 0$ be real and $k \le n$ natural numbers. For the
binomial kernel and a $\mathrm{Beta}(a, b)$ prior, the posterior distribution (Mathlib's posterior
kernel) after observing $k$ successes in $n$ trials is $\mathrm{Beta}(a + k, b + n - k)$. -/
theorem posterior_binomialKernel_betaMeasure (ha : 0 < a) (hb : 0 < b) {n k : ℕ} (hk : k ≤ n) :
    haveI := isProbabilityMeasureBeta ha hb
    ((binomialKernel n)†(betaMeasure a b)) k = betaMeasure (a + k) (b + (n - k : ℕ)) := by
  have := isProbabilityMeasureBeta ha hb
  have hc : 0 < (n.choose k : ℝ) * (beta (a + k) (b + (n - k : ℕ)) / beta a b) := by
    have := beta_pos ha hb
    have := beta_pos (α := a + k) (β := b + (n - k : ℕ)) (by positivity) (by positivity)
    have : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
    positivity
  have hev : (binomialKernel n ∘ₘ betaMeasure a b) {k} ≠ 0 := by
    rw [binomialKernel_comp_betaMeasure ha hb]
    exact (ENNReal.ofReal_pos.mpr hc).ne'
  rw [posterior_eq_bayesPosterior _ _ hev, bayesPosterior, withDensity_binomialKernel ha hb,
    binomialKernel_comp_betaMeasure ha hb, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top, one_smul]

/-- **Prior predictive probability of a success.** Let $a, b > 0$ be real. Under a
$\mathrm{Beta}(a, b)$ prior on the success probability, the probability that a single trial of the
binomial kernel succeeds is the prior mean $a / (a + b)$. -/
theorem binomialKernel_one_comp_betaMeasure (ha : 0 < a) (hb : 0 < b) :
    (binomialKernel 1 ∘ₘ betaMeasure a b) {1} = ENNReal.ofReal (a / (a + b)) := by
  rw [binomialKernel_comp_betaMeasure ha hb]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, Nat.cast_zero, add_zero, one_mul]
  rw [beta_add_one_left ha hb, mul_div_cancel_left₀ _ (beta_pos ha hb).ne']

/-- **Posterior predictive of the beta-binomial model.** Let $a, b > 0$ be real and $k \le n$
natural numbers. Under a $\mathrm{Beta}(a, b)$ prior on the success probability, after observing
$k$ successes in $n$ trials of the binomial kernel, the posterior predictive probability that one
further trial succeeds is $(a + k) / (a + b + n)$.

For $a = b = 1$ this is Laplace's rule of succession, $(k + 1) / (n + 2)$. -/
theorem posterior_predictive_betaMeasure (ha : 0 < a) (hb : 0 < b) {n k : ℕ} (hk : k ≤ n) :
    haveI := isProbabilityMeasureBeta ha hb
    (binomialKernel 1 ∘ₘ ((binomialKernel n)†(betaMeasure a b)) k) {1} =
      ENNReal.ofReal ((a + k) / (a + b + n)) := by
  have := isProbabilityMeasureBeta ha hb
  rw [posterior_binomialKernel_betaMeasure ha hb hk,
    binomialKernel_one_comp_betaMeasure (by positivity) (by positivity), Nat.cast_sub hk]
  congr 2
  ring

end Conjugacy

end Cslib.MachineLearning.Bayesian
