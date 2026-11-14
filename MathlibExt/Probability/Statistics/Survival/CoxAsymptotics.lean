/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.ProcessInference
public import MathlibExt.Probability.Statistics.Survival.ConcaveScore
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Cox regression: consistency and asymptotic normality (Andersen–Gill)

For each sample size `n`, the data `(Tᵢ, δᵢ, zᵢ)_{i < n}` (observed times, event indicators and a
scalar covariate) are random, `ω ↦ (T n ω, δ n ω, z n ω)` on a probability space `(Ω, P)`. Write
`ℓₙ` for the log partial likelihood `logPartialLikelihood₁`, `Uₙ = coxScore` for its derivative
and `Iₙ = coxInformation` for the observed information `-ℓₙ''` (see `CoxPartialLikelihood`). The
Cox estimator `βhat n` is a maximizer of `ℓₙ` whenever one exists (it need not exist: with
monotone likelihood there is none).

Andersen and Gill (1982) derive the asymptotics of `βhat n` from two limit statements about the
counting-process data, which they obtain from their conditions A–D by Rebolledo's martingale
central limit theorem (under a Lindeberg condition) and Lenglart's inequality. **These two limit
statements are the hypotheses here**; their derivation from conditions A–D is not formalized:

* (score CLT) `Uₙ(β₀) / √n ⟶ Z` in distribution, with `Z ~ N(0, v)`;
* (uniform information) on a neighbourhood `[β₀ - r, β₀ + r]`,
  `sup_b |Iₙ(b) / n - i(b)| → 0` in probability, for a function `i` continuous at `β₀` with
  `i(β₀) = v > 0`. The supremum is stated without measurability assumptions, as
  `P {ω | ∃ b ∈ [β₀ - r, β₀ + r], η ≤ |Iₙ(b) / n - i(b)|} → 0` for every `η > 0`.

That the score limit has variance `v` and the information limit is `v` reflects a shared limit,
not an identity between processes. In counting-process notation `Uₙ(β₀)` is a martingale whose
predictable variation integrates the risk-set variance against the compensator of the pooled
counting process; the observed information `Iₙ(β₀)` integrates the same variance against the
observed events. Under the Andersen–Gill conditions both, divided by `n`, converge in probability
to the same limit, and the limit of the predictable variation is the variance of the score limit.

## Main results

* `tendsto_measure_not_exists_isMaxOn`: with probability tending to one, `ℓₙ` has a maximizer.
* `tendstoInMeasure_coxMPLE` (**consistency**, Andersen–Gill Theorem 3.2): `βhat n → β₀` in
  probability. Only `Uₙ(β₀) / n → 0` in probability is used from the score hypothesis.
* `tendstoInDistribution_coxMPLE_gaussian` (**asymptotic normality**, Andersen–Gill Theorem
  3.3): `√n (βhat n - β₀) ⟶ Z / v` and `Z / v ~ N(0, v⁻¹)`: the asymptotic variance is the
  inverse of the limiting information. `tendstoInDistribution_coxMPLE` is the limit statement
  for an arbitrary score limit `Z`. Both assume the estimator is measurable,
  `AEMeasurable (βhat n) P`.
* `tendstoInMeasure_coxInformation_coxMPLE`: `Iₙ(βhat n) / n → v` in probability.
* `tendsto_coverage_cox_waldInterval_coxMPLE`: the Wald interval `βhat n ± c / √(Iₙ(βhat n))`
  has asymptotic coverage equal to the standard-normal mass of `[-c, c]`; this discharges the
  limit hypotheses of `ProcessInference.tendsto_coverage_cox_waldInterval`. It assumes the
  estimator and the model-based standard deviation `√(n / Iₙ(βhat n))` are measurable.

The deterministic core: `riskVar_nonneg` and `coxInformation_nonneg`, which give
`isConcaveScore_cox` (the scalar log partial likelihood is a concave criterion in the sense of
`ConcaveScore.IsConcaveScore`), then `antitone_coxScore`, `isMaxOn_of_coxScore_eq_zero` and
`coxScore_eq_zero_of_isMaxOn` (maximizers are the roots of the score),
`coxScore_eq_zero_and_abs_sub_lt` (a lower bound on the information near `β₀` and a small score
at `β₀` locate every maximizer near `β₀`), and `abs_sqrt_mul_sub_sub_le` (the one-step mean-value
expansion `√n (βhat - β₀) ≈ (Uₙ(β₀) / √n) / v`). The results from `antitone_coxScore` on, and the
Andersen–Gill theorems, are instances of the abstract results of `ConcaveScore`; the
probabilistic helper `tendstoInMeasure_div_sqrt` is proved there and re-exported here.

## Scope

Only a **scalar covariate** (`p = 1`) is treated. The vector case of Andersen–Gill (`β ∈ ℝᵖ`,
limit `N(0, Σ⁻¹)` with the information matrix `Σ`) needs the Jacobian of the score vector
`coxGradient` and a matrix-valued mean value argument, and is not covered. The derivation of the
two limit hypotheses from the counting-process conditions (Rebolledo's martingale CLT, Lenglart's
inequality, the uniform law for `S⁽ᵏ⁾ / n`) is not formalized.

## References

* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120, Theorems 3.2 and 3.3.
* D. R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972),
  187–220.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CoxAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.ConcaveScore

/-! ### Deterministic facts about the scalar Cox score -/

section Deterministic

variable {n : ℕ} (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ)

/-- The weighted risk-set variance is nonnegative. -/
theorem riskVar_nonneg (b : ℝ) (i : Fin n) : 0 ≤ riskVar T z b i := by
  have hW : 0 < ∑ l ∈ riskSet T i, exp (b * z l) :=
    sum_pos (fun _ _ => exp_pos _) (riskSet_nonempty T i)
  have hexp : ∑ l ∈ riskSet T i, exp (b * z l) * (z l - riskMean T z b i) ^ 2 =
      ∑ l ∈ riskSet T i, z l ^ 2 * exp (b * z l) -
        2 * riskMean T z b i * ∑ l ∈ riskSet T i, z l * exp (b * z l) +
          riskMean T z b i ^ 2 * ∑ l ∈ riskSet T i, exp (b * z l) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  have key : riskVar T z b i = (∑ l ∈ riskSet T i, exp (b * z l) * (z l - riskMean T z b i) ^ 2) /
      ∑ l ∈ riskSet T i, exp (b * z l) := by
    rw [hexp]
    simp only [riskVar, riskMean]
    generalize ∑ l ∈ riskSet T i, z l ^ 2 * exp (b * z l) = A at *
    generalize ∑ l ∈ riskSet T i, z l * exp (b * z l) = B at *
    generalize ∑ l ∈ riskSet T i, exp (b * z l) = W at *
    field_simp
    ring
  rw [key]
  exact div_nonneg (sum_nonneg fun l _ => by positivity) hW.le

/-- The observed information is nonnegative. -/
theorem coxInformation_nonneg (b : ℝ) : 0 ≤ coxInformation T δ z b :=
  sum_nonneg fun i _ => riskVar_nonneg T z b i

/-- The scalar Cox log partial likelihood is a concave criterion with the Cox score and
information, so the abstract results of `ConcaveScore` apply to it. -/
theorem isConcaveScore_cox :
    IsConcaveScore (logPartialLikelihood₁ T δ z) (coxScore T δ z) (coxInformation T δ z) :=
  ⟨hasDerivAt_logPartialLikelihood T δ z, hasDerivAt_coxScore T δ z, coxInformation_nonneg T δ z⟩

/-- The scalar Cox score is antitone (the log partial likelihood is concave). -/
theorem antitone_coxScore : Antitone (coxScore T δ z) :=
  (isConcaveScore_cox T δ z).antitone_score

/-- The scalar Cox score is continuous. -/
theorem continuous_coxScore : Continuous (coxScore T δ z) :=
  (isConcaveScore_cox T δ z).continuous_score

/-- Mean value form of the score increment: `U(b) - U(a) = -I(c) (b - a)` for some `c` between
`a` and `b`. -/
theorem exists_coxScore_sub_eq (a b : ℝ) :
    ∃ c ∈ Set.uIcc a b,
      coxScore T δ z b - coxScore T δ z a = -coxInformation T δ z c * (b - a) :=
  (isConcaveScore_cox T δ z).exists_score_sub_eq a b

/-- A maximizer of the scalar log partial likelihood is a root of the Cox score. -/
theorem coxScore_eq_zero_of_isMaxOn {b : ℝ} (h : IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b) :
    coxScore T δ z b = 0 :=
  (isConcaveScore_cox T δ z).score_eq_zero_of_isMaxOn h

/-- A root of the Cox score maximizes the scalar log partial likelihood (concavity). -/
theorem isMaxOn_of_coxScore_eq_zero {b : ℝ} (h : coxScore T δ z b = 0) :
    IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b :=
  (isConcaveScore_cox T δ z).isMaxOn_of_score_eq_zero h

/-- Signs of the score at `β₀ ± ε` from a lower bound `m` on the information near `β₀`: if
`|U(β₀)| < ε m` then `U(β₀ + ε) < 0 < U(β₀ - ε)`. -/
theorem coxScore_add_neg_and_sub_pos {β₀ ε m : ℝ} (hε : 0 < ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), m < coxInformation T δ z b)
    (hU : |coxScore T δ z β₀| < ε * m) :
    coxScore T δ z (β₀ + ε) < 0 ∧ 0 < coxScore T δ z (β₀ - ε) :=
  (isConcaveScore_cox T δ z).score_add_neg_and_sub_pos hε hI hU

/-- **Deterministic core of consistency.** If the information is bounded below by `m` on
`[β₀ - ε, β₀ + ε]` and `|U(β₀)| < ε m`, then the log partial likelihood has a maximizer, and any
`bh` that is a maximizer whenever one exists is a root of the score within `ε` of `β₀`. -/
theorem coxScore_eq_zero_and_abs_sub_lt {β₀ ε m bh : ℝ} (hε : 0 < ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), m < coxInformation T δ z b)
    (hU : |coxScore T δ z β₀| < ε * m)
    (hbh : (∃ b, IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ bh) :
    coxScore T δ z bh = 0 ∧ |bh - β₀| < ε :=
  (isConcaveScore_cox T δ z).score_eq_zero_and_abs_sub_lt hε hI hU hbh

/-- The normalized form of `coxScore_eq_zero_and_abs_sub_lt` used in the asymptotics: if
`|I(b) / n - i(b)| < v / 4` and `|i(b) - v| < v / 4` on `[β₀ - ε, β₀ + ε]` and
`|U(β₀) / n| < ε v / 4`, then `bh` is a root of the score within `ε` of `β₀`. -/
theorem coxScore_eq_zero_and_abs_sub_lt_of_div {i : ℝ → ℝ} {β₀ v ε bh : ℝ} (hn : 0 < n)
    (hv : 0 < v) (hε : 0 < ε) (hiv : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |i b - v| < v / 4)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |coxInformation T δ z b / n - i b| < v / 4)
    (hU : |coxScore T δ z β₀ / n| < ε * v / 4)
    (hbh : (∃ b, IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ T δ z) Set.univ bh) :
    coxScore T δ z bh = 0 ∧ |bh - β₀| < ε :=
  (isConcaveScore_cox T δ z).score_eq_zero_and_abs_sub_lt_of_div hn hv hε hiv hI hU hbh

/-- **Deterministic core of asymptotic normality.** If `bh` is a root of the score within `ε` of
`β₀` and the normalized information `I(b) / n` is within `η ≤ v / 2` of `v` on
`[β₀ - ε, β₀ + ε]`, then `√n (bh - β₀)` differs from `(U(β₀) / √n) / v` by at most
`|U(β₀) / √n| · 2 η / v²`. -/
theorem abs_sqrt_mul_sub_sub_le {β₀ ε v η bh : ℝ} (hn : 0 < n) (hv : 0 < v) (hη : η ≤ v / 2)
    (hroot : coxScore T δ z bh = 0) (hb : |bh - β₀| ≤ ε)
    (hI : ∀ b ∈ Set.Icc (β₀ - ε) (β₀ + ε), |coxInformation T δ z b / n - v| < η) :
    |√(n : ℝ) * (bh - β₀) - coxScore T δ z β₀ / √(n : ℝ) / v| ≤
      |coxScore T δ z β₀ / √(n : ℝ)| * (2 * η / v ^ 2) :=
  (isConcaveScore_cox T δ z).abs_sqrt_mul_sub_sub_le hn hv hη hroot hb hI

end Deterministic

/-! ### Probability helpers -/

-- `tendstoInMeasure_div_sqrt` is proved in `ConcaveScore`; the re-export keeps the name
-- `CoxAsymptotics.tendstoInMeasure_div_sqrt` available.
export MathlibExt.Probability.Statistics.ConcaveScore (tendstoInMeasure_div_sqrt)

section Probability

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}

/-- Dividing a centered Gaussian of variance `v ≠ 0` by `v` gives variance `v⁻¹`. -/
theorem hasLaw_div_gaussianReal {Z : Ω' → ℝ} {v : NNReal} (hv : v ≠ 0)
    (hZ : HasLaw Z (gaussianReal 0 v) P') :
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 v⁻¹) P' := by
  have h : HasLaw (fun x : ℝ => x / (v : ℝ)) (gaussianReal 0 v⁻¹) (gaussianReal 0 v) := by
    have := hasLaw_map (P := gaussianReal 0 v) (X := fun x : ℝ => x / (v : ℝ)) (by fun_prop)
    rwa [gaussianReal_map_div_const, zero_div,
      show v / NNReal.mk ((v : ℝ) ^ 2) (sq_nonneg _) = v⁻¹ by
        ext; simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_inv]
        have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
        field_simp] at this
  exact h.comp hZ

end Probability

/-! ### The Andersen–Gill theorems for a scalar covariate -/

section AndersenGill

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T : (n : ℕ) → Ω → Fin n → ℝ} {δ : (n : ℕ) → Ω → Fin n → Bool}
  {z : (n : ℕ) → Ω → Fin n → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {Z : Ω' → ℝ}
  {v : NNReal}

/-- **With probability tending to one the Cox estimator is a root of the score near `β₀`.**
Under the Andersen–Gill hypotheses (score limit at `β₀`, uniform convergence in probability of
`I_n(b) / n` to a function `i` continuous at `β₀` with `i β₀ = v > 0`), for every `ε > 0` the
probability that `βhat n` fails to be a root of the score within `ε` of `β₀` tends to zero. -/
theorem tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ¬ (coxScore (T n ω) (δ n ω) (z n ω) (βhat n ω) = 0 ∧
      |βhat n ω - β₀| < ε)}) atTop (𝓝 0) :=
  tendsto_measure_not_score_eq_zero_and_abs_sub_lt
    (fun n ω => isConcaveScore_cox (T n ω) (δ n ω) (z n ω))
    hv hβhat hscore hi hiv hinfo hr hε

/-- **Existence of the Cox estimator with probability tending to one** (Andersen–Gill): under the
hypotheses of `tendsto_measure_not_coxScore_eq_zero_and_abs_sub_lt`, the probability that the
scalar log partial likelihood has no maximizer tends to zero. -/
theorem tendsto_measure_not_exists_isMaxOn (hv : v ≠ 0)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∃ b,
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b}) atTop (𝓝 0) :=
  ConcaveScore.tendsto_measure_not_exists_isMaxOn
    (fun n ω => isConcaveScore_cox (T n ω) (δ n ω) (z n ω))
    hv hscore hi hiv hinfo hr

/-- **Consistency of the Cox estimator** (Andersen–Gill 1982, Theorem 3.2, scalar covariate).
Let `βhat n` be a maximizer of the log partial likelihood of the first `n` subjects whenever one
exists. Assume

* the normalized score at the true coefficient converges in distribution,
  `U_n(β₀) / √n ⟶ Z` (the Andersen–Gill martingale central limit theorem under the Lindeberg
  condition; only `U_n(β₀) / n → 0` in probability is used here), and
* the normalized information converges uniformly in probability on a neighbourhood
  `[β₀ - r, β₀ + r]`, `sup_b |I_n(b) / n - i(b)| → 0`, to a function `i` continuous at `β₀`
  with `i(β₀) = v > 0`.

Then `βhat n → β₀` in probability. -/
theorem tendstoInMeasure_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) :=
  tendstoInMeasure_argmax
    (fun n ω => isConcaveScore_cox (T n ω) (δ n ω) (z n ω))
    hv hβhat hscore hi hiv hinfo hr

/-- **The Cox estimator is asymptotically `Z / v`.** Under the hypotheses of
`tendstoInMeasure_coxMPLE` and measurability of the estimator, `√n (βhat n - β₀) ⟶ Z / v` in
distribution, where `Z` is the limit of `Uₙ(β₀) / √n` and `v = i(β₀)` the limiting information.
No Gaussianity is used; see `tendstoInDistribution_coxMPLE_gaussian` for the normal limit. -/
theorem tendstoInDistribution_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' :=
  tendstoInDistribution_argmax
    (fun n ω => isConcaveScore_cox (T n ω) (δ n ω) (z n ω))
    hv hβhat hβhat_meas hscore hi hiv hinfo hr

/-- **Asymptotic normality of the Cox estimator** (Andersen–Gill 1982, Theorem 3.3, scalar
covariate). Let `βhat n` be a measurable maximizer of the log partial likelihood whenever one
exists. If `Uₙ(β₀) / √n ⟶ Z ~ N(0, v)` and `Iₙ(b) / n → i(b)` uniformly in probability near `β₀`
with `i` continuous at `β₀` and `i(β₀) = v ≠ 0`, then `√n (βhat n - β₀) ⟶ Z / v` in distribution
and `Z / v ~ N(0, v⁻¹)`: the asymptotic variance is the inverse of the information. -/
theorem tendstoInDistribution_coxMPLE_gaussian (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' ∧
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 v⁻¹) P' :=
  ⟨tendstoInDistribution_coxMPLE hv hβhat hβhat_meas hscore hi hiv hinfo hr,
    hasLaw_div_gaussianReal hv hZ⟩

/-- **Consistency of the normalized observed information at the estimator.** Under the
hypotheses of `tendstoInMeasure_coxMPLE`, `Iₙ(βhat n) / n → v` in probability. -/
theorem tendstoInMeasure_coxInformation_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P (fun n ω => coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω) / n) atTop
      (fun _ => (v : ℝ)) :=
  tendstoInMeasure_info_argmax
    (fun n ω => isConcaveScore_cox (T n ω) (δ n ω) (z n ω))
    hv hβhat hscore hi hiv hinfo hr

/-- **Coverage of the Cox Wald interval under the Andersen–Gill conditions.** Under the hypotheses
of `tendstoInDistribution_coxMPLE_gaussian` (including the Gaussian law `hZ` of the score limit
and measurability of `βhat n`), and assuming the model-based standard deviation
`√(n / Iₙ(βhat n))` is a.e.-measurable (`hsd_meas`), the Wald interval
`βhat n ± c / √(Iₙ(βhat n))` covers the true coefficient `β₀` with probability tending to the
standard-normal mass of `[-c, c]`. This discharges the two limit hypotheses of
`ProcessInference.tendsto_coverage_cox_waldInterval`
(the estimator limit and the consistency of the model-based standard deviation). -/
theorem tendsto_coverage_cox_waldInterval_coxMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ coxScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r)
    (hsd_meas : ∀ n : ℕ, AEMeasurable
      (fun ω ↦ √(n / coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω))) P) (c : ℝ) :
    Tendsto (fun n : ℕ ↦ P.real {ω | β₀ ∈ ProcessInference.waldInterval (βhat n ω)
        (1 / √(coxInformation (T n ω) (δ n ω) (z n ω) (βhat n ω))) c}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-c) c))) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hAN := tendstoInDistribution_coxMPLE hv hβhat hβhat_meas hscore hi hiv hinfo hr
  have hsd := (tendstoInMeasure_coxInformation_coxMPLE hv hβhat hscore hi hiv hinfo hr
    ).comp_const_of_continuousAt (f := fun x => √(x⁻¹)) ((continuousAt_inv₀ hv').sqrt)
  refine ProcessInference.tendsto_coverage_cox_waldInterval (inv_ne_zero hv) c hAN
    (hasLaw_div_gaussianReal hv hZ) ?_ hsd_meas
  convert hsd using 3 with n ω
  · rw [inv_div]
  · simp

end AndersenGill

end MathlibExt.Probability.Statistics.CoxAsymptotics
