/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.NegativeBinomial
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.Variance

import MathlibExt.Probability.Distributions.Gamma
import MathlibExt.Probability.Distributions.GammaMoments

/-!
# Gamma–Poisson hierarchical counts and empirical-Bayes shrinkage

A count `k` of one gene in one cell with size factor (exposure) `s > 0` is modeled as
`k ∣ λ ~ Po(s λ)` with a Gamma prior `λ ~ Gamma(a, b)` (shape `a > 0`, rate `b > 0`) on the
gene's expression rate. This is the Gamma–Poisson (negative binomial) hierarchy behind
empirical-Bayes shrinkage of single-cell and bulk RNA-seq counts (Robbins 1956; Morris 1983;
Sarkar and Stephens 2021). This file formalizes that one model: conjugacy, the shrinkage form of
the posterior mean with its boundary cases, and method-of-moments estimation of the
hyperparameters with its consistency. It is not a single-cell pipeline: normalization, size
factor estimation, multi-gene sharing, pseudotime and RNA velocity are out of scope.

## Main definitions

* `poissonExposureLik s k r`: the `Po(s r)` mass `e^{-s r} (s r)ᵏ / k!`.
* `marginalLik a b s k`: the marginal likelihood `∫ P(k ∣ r) dGamma(a, b)`.
* `posteriorMean a b s k = (a + k) / (b + s)`, `shrinkageWeight b s = s / (b + s)`.
* `momShape M V = M² / (V - M)`, `momRate s M V = s M / (V - M)`: moment estimates.
* `ebPosteriorMean s M V k`: the posterior mean at the moment estimates.
* `sampleMean`, `sampleVar`: empirical moments of the first `n` counts.

## Main results

* `posterior_eq_gammaPDFReal`: **conjugacy.** The posterior is `Gamma(a + k, b + s)`; at `s = 1`
  this is `ProbabilityTheory.gammaPDFReal_posterior`, whose proof it follows through the shared
  Gamma integral `ProbabilityTheory.integral_pow_mul_exp_neg_mul_gammaMeasure`.
* `marginalLik_eq_negBinomialReal`: the marginal law is `NB(a, s a / b)`.
* `integral_id_posterior`, `variance_posterior`: posterior mean and variance.
* `posteriorMean_eq_shrinkage`, `posteriorMean_mem_segment`: the posterior mean is
  `w (k / s) + (1 - w) (a / b)` with `w = s / (b + s) ∈ (0, 1)`.
* `posteriorMean_zero`, `posteriorMean_zero_mem_Ioo`: a zero count gives `a / (b + s)`, strictly
  between `0` and the prior mean.
* `tendsto_shrinkageWeight_zero`, `tendsto_posteriorMean_priorVariance_atTop`: no-shrinkage
  limit (`w → 1`, posterior mean `→ k / s` as the prior variance `→ ∞`);
  `tendsto_posteriorMean_priorVariance_zero`: full shrinkage to the prior mean as it `→ 0`.
* `mom_moment_equations`, `eq_mom_of_moment_equations`: the moment estimates are the unique
  positive solution of the moment equations; `mom_marginal_moments`: Fisher consistency.
* `ae_tendsto_mom`: **strong consistency.** For i.i.d. counts with the marginal moments, the
  moment estimates converge a.s. to `(a, b)` and the empirical-Bayes posterior mean to the
  oracle posterior mean.

## Implementation notes

The count law of a random variable is not formalized here; `ae_tendsto_mom` takes the first two
moments of the marginal law as hypotheses, which `marginalLik_eq_negBinomialReal` together with
`ProbabilityTheory.hasSum_mul_negBinomialReal` and `ProbabilityTheory.hasSum_sq_negBinomialReal`
supply at the pmf level.

Reuse (search of `MathlibExt` on 2026-11-11 for conjugacy, shrinkage, empirical Bayes and method
of moments): no shrinkage or empirical-Bayes development existed. Conjugacy follows
`ProbabilityTheory.gammaPDFReal_posterior`
(`MathlibExt.Probability.Distributions.NegativeBinomial`), the Gamma moments are
`ProbabilityTheory.integral_id_gammaMeasure` and `ProbabilityTheory.variance_id_gammaMeasure`,
the negative binomial moments are reused from the same file, and the strong law is Mathlib's
`ProbabilityTheory.strong_law_ae`.

## References

* H. Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math.
  Statist. Prob. 1 (1956), 157–163.
* C. N. Morris, *Parametric empirical Bayes inference: theory and applications*, J. Amer.
  Statist. Assoc. 78 (1983), 47–55.
* A. Sarkar and M. Stephens, *Separating measurement and expression models clarifies confusion
  in single-cell RNA sequencing analysis*, Nat. Genet. 53 (2021), 770–777.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Polynomial Topology Function
open scoped Nat

namespace MathlibExt.Biology.Omics.HierarchicalCount

/-- The Poisson likelihood of a count `k` at rate `r` and size factor (exposure) `s`:
`P(k ∣ r) = e^{-s r} (s r)ᵏ / k!`, the mass of `k` under `Po(s r)`. -/
noncomputable def poissonExposureLik (s : ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  exp (-(s * r)) * (s * r) ^ k / k !

/-- The marginal (prior-predictive) likelihood of a count `k` under the hierarchy
`k ∣ λ ~ Po(s λ)`, `λ ~ Gamma(a, b)`: `∫ P(k ∣ r) dGamma(a, b)(r)`. -/
noncomputable def marginalLik (a b s : ℝ) (k : ℕ) : ℝ :=
  ∫ r, poissonExposureLik s k r ∂gammaMeasure a b

/-- Closed form of the marginal likelihood: `a⁽ᵏ⁾ sᵏ bᵃ / ((b + s) ^ (a + k) k!)`. -/
theorem marginalLik_eq {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) (k : ℕ) :
    marginalLik a b s k =
      (ascPochhammer ℝ k).eval a * s ^ k * b ^ a / (b + s) ^ (a + k) / k ! := by
  have h := integral_pow_mul_exp_neg_mul_gammaMeasure ha hb hs k
  rw [marginalLik]
  have : (fun r => poissonExposureLik s k r) =
      fun r => (s ^ k / k !) * (r ^ k * exp (-(s * r))) := by
    funext r; rw [poissonExposureLik, mul_pow]; ring
  rw [this, integral_const_mul, h]
  ring

/-- **Marginal of the hierarchy is negative binomial (Greenwood–Yule with exposure).** For
`a, b > 0` and `s ≥ 0`, the count's marginal law is `NB(a, s a / b)`: size `a`, mean `s a / b`. -/
theorem marginalLik_eq_negBinomialReal {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s)
    (k : ℕ) : marginalLik a b s k = negBinomialReal a (s * a / b) k := by
  rw [marginalLik_eq ha hb hs, negBinomialReal]
  have hbs : 0 < b + s := by linarith
  have h1 : a / (a + s * a / b) = b / (b + s) := by field_simp
  have h2 : s * a / b / (a + s * a / b) = s / (b + s) := by field_simp
  rw [h1, h2, Real.div_rpow hb.le hbs.le, Real.rpow_add hbs, Real.rpow_natCast, div_pow]
  have : (b + s) ^ a ≠ 0 := (Real.rpow_pos_of_pos hbs a).ne'
  have : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  field_simp

/-- **Gamma–Poisson conjugacy with exposure.** With prior `λ ~ Gamma(a, b)` (`a, b > 0`) and one
count `k ~ Po(s λ)` (`s > 0`), the posterior density (likelihood times prior density over the
marginal likelihood) is the `Gamma(a + k, b + s)` density. At `s = 1` this is
`ProbabilityTheory.gammaPDFReal_posterior`. -/
theorem posterior_eq_gammaPDFReal {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (k : ℕ)
    (r : ℝ) :
    poissonExposureLik s k r * gammaPDFReal a b r / marginalLik a b s k =
      gammaPDFReal (a + k) (b + s) r := by
  rw [marginalLik_eq ha hb hs.le]
  rcases lt_or_ge r 0 with hr | hr
  · simp [gammaPDFReal, not_le.2 hr]
  have hbs : 0 < b + s := by linarith
  have hP := ascPochhammer_pos k a ha
  have hk : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hba : b ^ a ≠ 0 := (Real.rpow_pos_of_pos hb a).ne'
  have hbsa : (b + s) ^ (a + k) ≠ 0 := (Real.rpow_pos_of_pos hbs _).ne'
  have hsk : s ^ k ≠ 0 := pow_ne_zero _ hs.ne'
  have hG : Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  simp only [gammaPDFReal, poissonExposureLik, ite_eq_left hr]
  rw [Gamma_add_nat_eq ha, ← pow_mul_rpow_sub_one hr ha k]
  have he : exp (-((b + s) * r)) = exp (-(s * r)) * exp (-(b * r)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he, mul_pow]
  field_simp

/-- The posterior mean `(a + k) / (b + s)` of the rate `λ` after observing `k ~ Po(s λ)` under
the prior `λ ~ Gamma(a, b)`. -/
noncomputable def posteriorMean (a b s : ℝ) (k : ℕ) : ℝ := (a + k) / (b + s)

/-- The shrinkage weight `w = s / (b + s)` on the per-cell estimate `k / s`; the prior mean
`a / b` gets weight `1 - w = b / (b + s)`. It depends only on the prior rate `b` and the size
factor `s`. -/
noncomputable def shrinkageWeight (b s : ℝ) : ℝ := s / (b + s)

/-- The posterior law `Gamma(a + k, b + s)` has mean `posteriorMean a b s k`. -/
theorem integral_id_posterior {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) (k : ℕ) :
    ∫ x, x ∂gammaMeasure (a + k) (b + s) = posteriorMean a b s k :=
  integral_id_gammaMeasure (by positivity) (by linarith)

/-- The posterior law `Gamma(a + k, b + s)` has variance `(a + k) / (b + s) ^ 2`. -/
theorem variance_posterior {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s) (k : ℕ) :
    variance id (gammaMeasure (a + k) (b + s)) = (a + k) / (b + s) ^ 2 :=
  variance_id_gammaMeasure (by positivity) (by linarith)

/-- The shrinkage weight lies strictly between `0` and `1` for `b, s > 0`. -/
theorem shrinkageWeight_mem_Ioo {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    shrinkageWeight b s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hbs : 0 < b + s := by linarith
  refine ⟨div_pos hs hbs, (div_lt_one hbs).2 (by linarith)⟩

/-- `1 - w = b / (b + s)`. -/
theorem one_sub_shrinkageWeight {b s : ℝ} (hbs : 0 < b + s) :
    1 - shrinkageWeight b s = b / (b + s) := by
  rw [shrinkageWeight]; field_simp; ring

/-- **The posterior mean is a convex shrinkage combination.** For `b, s > 0`, the posterior mean
is `w · (k / s) + (1 - w) · (a / b)` with `w = s / (b + s)`: the per-cell estimate `k / s` shrunk
toward the prior mean `a / b`. -/
theorem posteriorMean_eq_shrinkage {a b s : ℝ} (hb : 0 < b) (hs : 0 < s) (k : ℕ) :
    posteriorMean a b s k =
      shrinkageWeight b s * (k / s) + (1 - shrinkageWeight b s) * (a / b) := by
  have hbs : 0 < b + s := by linarith
  rw [one_sub_shrinkageWeight hbs, posteriorMean, shrinkageWeight]
  field_simp
  ring

/-- The posterior mean lies on the segment between the prior mean `a / b` and the per-cell
estimate `k / s`. -/
theorem posteriorMean_mem_segment {a b s : ℝ} (hb : 0 < b) (hs : 0 < s) (k : ℕ) :
    posteriorMean a b s k ∈ segment ℝ (a / b) (k / s) := by
  obtain ⟨hw0, hw1⟩ := shrinkageWeight_mem_Ioo hb hs
  refine ⟨1 - shrinkageWeight b s, shrinkageWeight b s, by linarith, hw0.le, by ring, ?_⟩
  rw [posteriorMean_eq_shrinkage hb hs, smul_eq_mul, smul_eq_mul]
  ring

/-- **Zero count.** With `k = 0` the per-cell estimate is `0` and the posterior mean is the
shrunk prior mean `(1 - w) (a / b) = a / (b + s)`. -/
theorem posteriorMean_zero {a b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    posteriorMean a b s 0 = (1 - shrinkageWeight b s) * (a / b) := by
  simpa using posteriorMean_eq_shrinkage (a := a) hb hs 0

/-- **Zero count, strict bounds.** A zero count gives a posterior mean that is strictly
positive (the rate is not estimated as `0`) and strictly below the prior mean. -/
theorem posteriorMean_zero_mem_Ioo {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    posteriorMean a b s 0 ∈ Set.Ioo 0 (a / b) := by
  have hbs : 0 < b + s := by linarith
  simp only [posteriorMean, Nat.cast_zero, add_zero]
  exact ⟨div_pos ha hbs, div_lt_div_of_pos_left ha hb (by linarith)⟩

/-- **No-shrinkage limit, weight.** As the prior rate `b → 0⁺` (prior variance `a / b² → ∞` at
fixed prior mean), the shrinkage weight tends to `1`. -/
theorem tendsto_shrinkageWeight_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun b => shrinkageWeight b s) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun b => s / (b + s)) (𝓝 0) (𝓝 (s / (0 + s))) :=
    tendsto_const_nhds.div (tendsto_id.add tendsto_const_nhds) (by simpa using hs.ne')
  rw [zero_add, div_self hs.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **No-shrinkage limit, posterior mean.** Parametrize the Gamma prior by its mean `m` and
variance `v` (shape `m² / v`, rate `m / v`). As the prior variance `v → ∞` the posterior mean
tends to the per-cell estimate `k / s`. -/
theorem tendsto_posteriorMean_priorVariance_atTop (m : ℝ) {s : ℝ} (hs : 0 < s) (k : ℕ) :
    Tendsto (fun v => posteriorMean (m ^ 2 / v) (m / v) s k) atTop (𝓝 (k / s)) := by
  have h1 : Tendsto (fun v : ℝ => m ^ 2 / v) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun v : ℝ => m / v) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h := (h1.add (tendsto_const_nhds (x := (k : ℝ)))).div (h2.add (tendsto_const_nhds (x := s)))
    (by simpa using hs.ne')
  simpa [posteriorMean, Pi.div_def] using h

/-- **Full-shrinkage limit.** At fixed prior mean `m`, as the prior variance `v → 0⁺` the
posterior mean tends to the prior mean `m`, whatever the count. -/
theorem tendsto_posteriorMean_priorVariance_zero {m s : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (k : ℕ) :
    Tendsto (fun v => posteriorMean (m ^ 2 / v) (m / v) s k) (𝓝[>] 0) (𝓝 m) := by
  have hev : (fun v : ℝ => (m ^ 2 + k * v) / (m + s * v)) =ᶠ[𝓝[>] 0]
      fun v => posteriorMean (m ^ 2 / v) (m / v) s k := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv : (0 : ℝ) < v := hv
    have : 0 < m + s * v := by positivity
    rw [posteriorMean]
    field_simp
  refine Tendsto.congr' hev ?_
  have hn : Tendsto (fun v : ℝ => m ^ 2 + k * v) (𝓝 0) (𝓝 (m ^ 2 + k * 0)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).tendsto 0)
  have hd : Tendsto (fun v : ℝ => m + s * v) (𝓝 0) (𝓝 (m + s * 0)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).tendsto 0)
  have h := hn.div hd (by simpa using hm.ne')
  have hlim : (m ^ 2 + k * 0) / (m + s * 0) = m := by
    rw [mul_zero, mul_zero, add_zero, add_zero, sq, mul_div_assoc, div_self hm.ne', mul_one]
  rw [hlim] at h
  exact (h.mono_left nhdsWithin_le_nhds :)

/-! ### Empirical Bayes: method-of-moments hyperparameters -/

/-- Method-of-moments shape estimate `â = M² / (V - M)` from a count mean `M` and variance `V`.
It inverts the negative binomial variance law `V = M + M² / a`. -/
noncomputable def momShape (M V : ℝ) : ℝ := M ^ 2 / (V - M)

/-- Method-of-moments rate estimate `b̂ = s M / (V - M)` for size factor `s`, from a count mean
`M` and variance `V`. It inverts `M = s a / b` at `a = momShape M V`. -/
noncomputable def momRate (s M V : ℝ) : ℝ := s * M / (V - M)

/-- **Defining equations of the moment estimator.** If the counts are overdispersed
(`0 < M < V`) and `s > 0`, the estimates `(â, b̂)` reproduce the observed moments under the
hierarchy: marginal mean `s â / b̂ = M` and marginal variance `M + M² / â = V`. -/
theorem mom_moment_equations {s M V : ℝ} (hs : 0 < s) (hM : 0 < M) (hMV : M < V) :
    s * momShape M V / momRate s M V = M ∧ M + M ^ 2 / momShape M V = V := by
  have hVM : 0 < V - M := by linarith
  refine ⟨?_, ?_⟩
  · rw [momShape, momRate]; field_simp
  · rw [momShape]; field_simp; ring

/-- **Uniqueness.** Positive hyperparameters `(a, b)` that solve the moment equations
`s a / b = M`, `M + M² / a = V` are the moment estimates. -/
theorem eq_mom_of_moment_equations {a b s M V : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hmean : s * a / b = M) (hvar : M + M ^ 2 / a = V) :
    a = momShape M V ∧ b = momRate s M V := by
  subst hmean hvar
  have hM : 0 < s * a / b := by positivity
  refine ⟨?_, ?_⟩
  · rw [momShape, add_sub_cancel_left]; field_simp
  · rw [momRate, add_sub_cancel_left]; field_simp

/-- **Fisher consistency.** Evaluated at the population mean and variance of the hierarchy's
marginal law `marginalLik a b s = NB(a, s a / b)` (proved moments
`ProbabilityTheory.hasSum_mul_negBinomialReal`, `ProbabilityTheory.variance_negBinomial`), the
moment estimates return the true hyperparameters `(a, b)`. -/
theorem mom_marginal_moments {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    momShape (∑' k : ℕ, (k : ℝ) * marginalLik a b s k)
        (∑' k : ℕ, (k : ℝ) ^ 2 * marginalLik a b s k -
          (∑' k : ℕ, (k : ℝ) * marginalLik a b s k) ^ 2) = a ∧
      momRate s (∑' k : ℕ, (k : ℝ) * marginalLik a b s k)
        (∑' k : ℕ, (k : ℝ) ^ 2 * marginalLik a b s k -
          (∑' k : ℕ, (k : ℝ) * marginalLik a b s k) ^ 2) = b := by
  have hμ : 0 ≤ s * a / b := by positivity
  simp only [funext (marginalLik_eq_negBinomialReal ha hb hs.le)]
  rw [variance_negBinomial ha hμ, (hasSum_mul_negBinomialReal ha hμ).tsum_eq]
  exact (eq_mom_of_moment_equations ha hb hs rfl rfl).imp Eq.symm Eq.symm

/-- The empirical-Bayes posterior mean: the posterior mean `(â + k) / (b̂ + s)` with the
hyperparameters replaced by their moment estimates from a count mean `M` and variance `V`. -/
noncomputable def ebPosteriorMean (s M V : ℝ) (k : ℕ) : ℝ :=
  posteriorMean (momShape M V) (momRate s M V) s k

/-- The empirical-Bayes posterior mean is a convex shrinkage combination of `k / s` and the
plug-in prior mean `â / b̂ = M / s`, with weight `s / (b̂ + s)`, whenever `0 < M < V`. -/
theorem ebPosteriorMean_eq_shrinkage {s M V : ℝ} (hs : 0 < s) (hM : 0 < M) (hMV : M < V)
    (k : ℕ) :
    ebPosteriorMean s M V k = shrinkageWeight (momRate s M V) s * (k / s) +
      (1 - shrinkageWeight (momRate s M V) s) * (M / s) := by
  have hVM : 0 < V - M := by linarith
  have hb : 0 < momRate s M V := div_pos (mul_pos hs hM) hVM
  rw [ebPosteriorMean, posteriorMean_eq_shrinkage hb hs]
  congr 2
  rw [momShape, momRate]; field_simp

/-- The sample mean `M̂ₙ = n⁻¹ ∑_{i<n} Xᵢ` of the first `n` counts. -/
noncomputable def sampleMean {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω

/-- The (biased, divisor `n`) sample variance `V̂ₙ = n⁻¹ ∑_{i<n} Xᵢ² - M̂ₙ²` of the first `n`
counts. -/
noncomputable def sampleVar {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω ^ 2 - sampleMean X n ω ^ 2

/-- Deterministic core of consistency: the moment estimates and the empirical-Bayes posterior
mean are continuous at overdispersed moments, so they converge when the sample mean and
second moment converge. -/
theorem tendsto_mom_of_tendsto {ι : Type*} {l : Filter ι} {Mn Qn : ι → ℝ} {M Q s : ℝ}
    (hs : 0 < s) (hM : 0 < M) (hMV : M < Q - M ^ 2) (hMn : Tendsto Mn l (𝓝 M))
    (hQn : Tendsto Qn l (𝓝 Q)) :
    Tendsto (fun i => momShape (Mn i) (Qn i - Mn i ^ 2)) l (𝓝 (momShape M (Q - M ^ 2))) ∧
      Tendsto (fun i => momRate s (Mn i) (Qn i - Mn i ^ 2)) l
        (𝓝 (momRate s M (Q - M ^ 2))) ∧
      ∀ k : ℕ, Tendsto (fun i => ebPosteriorMean s (Mn i) (Qn i - Mn i ^ 2) k) l
        (𝓝 (ebPosteriorMean s M (Q - M ^ 2) k)) := by
  have hden : Tendsto (fun i => Qn i - Mn i ^ 2 - Mn i) l (𝓝 (Q - M ^ 2 - M)) :=
    (hQn.sub (hMn.pow 2)).sub hMn
  have hne : Q - M ^ 2 - M ≠ 0 := by linarith
  have hA := (hMn.pow 2).div hden hne
  have hB := (hMn.const_mul s).div hden hne
  have hb : 0 < momRate s M (Q - M ^ 2) := div_pos (mul_pos hs hM) (by linarith)
  refine ⟨hA, hB, fun k => ?_⟩
  exact (hA.add tendsto_const_nhds).div (hB.add tendsto_const_nhds) (by linarith)

/-- **Strong consistency of the empirical-Bayes hyperparameters.** Let `X₀, X₁, …` be pairwise
independent, identically distributed counts with finite second moment whose mean and second
moment are those of the hierarchy's marginal law `NB(a, s a / b)`: `E X₀ = s a / b` and
`E X₀² = μ + μ² / a + μ²` with `μ = s a / b`. Then almost surely the moment estimates computed
from the first `n` counts converge to `(a, b)`, and for every count `k` the empirical-Bayes
posterior mean converges to the oracle posterior mean `(a + k) / (b + s)`.

The moment hypotheses are where the count model enters: they are exactly the pmf-level facts
`ProbabilityTheory.hasSum_mul_negBinomialReal` and `ProbabilityTheory.hasSum_sq_negBinomialReal`
for `marginalLik a b s = NB(a, s a / b)` (`marginalLik_eq_negBinomialReal`), transported to a
random variable whose law is that pmf. -/
theorem ae_tendsto_mom {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (hint : Integrable (X 0) μ) (hint2 : Integrable (fun ω => X 0 ω ^ 2) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : μ[X 0] = s * a / b)
    (hsq : μ[fun ω => X 0 ω ^ 2] = s * a / b + (s * a / b) ^ 2 / a + (s * a / b) ^ 2) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => momShape (sampleMean X n ω) (sampleVar X n ω)) atTop (𝓝 a) ∧
      Tendsto (fun n => momRate s (sampleMean X n ω) (sampleVar X n ω)) atTop (𝓝 b) ∧
      ∀ k : ℕ, Tendsto (fun n => ebPosteriorMean s (sampleMean X n ω) (sampleVar X n ω) k)
        atTop (𝓝 (posteriorMean a b s k)) := by
  have h1 := strong_law_ae X hint hindep hident
  have hmeas : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have h2 := strong_law_ae (fun i ω => X i ω ^ 2) hint2
    (fun i j hij => (hindep hij).comp hmeas hmeas) (fun i => (hident i).comp hmeas)
  filter_upwards [h1, h2] with ω hω1 hω2
  simp only [smul_eq_mul] at hω1 hω2
  rw [hmean] at hω1
  rw [hsq] at hω2
  set m := s * a / b with hm
  have hm0 : 0 < m := by positivity
  have hMV : m < m + m ^ 2 / a + m ^ 2 - m ^ 2 := by
    have : 0 < m ^ 2 / a := by positivity
    linarith
  obtain ⟨hA, hB, hC⟩ := tendsto_mom_of_tendsto hs hm0 hMV hω1 hω2
  obtain ⟨ha', hb'⟩ := eq_mom_of_moment_equations ha hb hs hm.symm
    (show m + m ^ 2 / a = m + m ^ 2 / a + m ^ 2 - m ^ 2 by ring)
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [ha']; exact hA
  · rw [hb']; exact hB
  · have := hC k
    rw [ebPosteriorMean, ← ha', ← hb'] at this
    exact this

end MathlibExt.Biology.Omics.HierarchicalCount
