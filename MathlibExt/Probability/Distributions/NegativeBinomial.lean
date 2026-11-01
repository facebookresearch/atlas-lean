/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonMixture
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.RingTheory.Polynomial.Pochhammer

import MathlibExt.Probability.Distributions.Gamma

/-!
# The negative binomial distribution as a Gamma–Poisson mixture

The negative binomial law with size `θ > 0` and mean `μ ≥ 0` has mass function

`NB(k; θ, μ) = θ⁽ᵏ⁾ / k! · (θ / (θ + μ)) ^ θ · (μ / (θ + μ)) ^ k`,

where `θ⁽ᵏ⁾ = θ (θ + 1) ⋯ (θ + k - 1) = Γ(θ + k) / Γ(θ)` is the rising factorial
(`ascPochhammer`). Greenwood and Yule (1920) obtained it as a Poisson law whose rate is
Gamma-distributed; it is the standard model of overdispersed counts in single-cell RNA
sequencing (Townes et al. 2019) and the stationary law of bursty gene expression (Shahrezaei and
Swain 2008).

## Main definitions

* `ProbabilityTheory.negBinomialReal θ μ k`: the mass function `NB(k; θ, μ)`.
* `ProbabilityTheory.immigrationDeathFlow κ γ p n`: the net probability flow into state `n` of
  the immigration–death chain (inflow `κ`, outflow `γ` per molecule).
* `ProbabilityTheory.burstDeathFlow κ γ b p n`: the same for production in geometric bursts of
  mean size `b`.

## Main results

* The generic Gamma lemmas (`integral_pow_mul_exp_neg_mul_gammaMeasure`:
  `∫ xᵏ e^{-c x} dGamma(a, b) = a⁽ᵏ⁾ bᵃ / (b + c) ^ (a + k)`, Gamma moments) live in
  `MathlibExt.Probability.Distributions.Gamma`.
* `poissonMixtureReal_gammaMeasure`: **Greenwood–Yule.** The Poisson mixture over
  `Gamma(shape a, rate b)` is `NB(a, a / b)`.
* `hasSum_negBinomialReal`, `hasSum_mul_negBinomialReal`, `variance_negBinomial`: normalization,
  mean `μ` and variance `μ + μ² / θ`.
* `exp_neg_le_negBinomialReal_zero`: `P(0) = (θ / (θ + μ)) ^ θ ≥ e^{-μ}`.
* `gammaPDFReal_posterior`, `posterior_predictive_gammaPoisson`: **Gamma–Poisson conjugacy.**
  After observing `k` from `Po(Λ)`, `Λ ~ Gamma(a, b)`, the posterior is `Gamma(a + k, b + 1)` and
  the posterior predictive law of a new count is `NB(a + k, (a + k) / (b + 1))`.
* `immigrationDeathFlow_poisson`: the Poisson law `Po(κ / γ)` is stationary for the
  immigration–death chain; `fano_poisson`: its Fano factor is `1`.
* `burstDeathFlow_negBinomial`: `NB(κ / γ, κ b / γ)` is stationary for bursty production;
  `fano_negBinomial`: its Fano factor is `1 + b`.

## References

* M. Greenwood and G. U. Yule, *An inquiry into the nature of frequency distributions
  representative of multiple happenings*, J. R. Statist. Soc. 83 (1920), 255–279.
* F. W. Townes, S. C. Hicks, M. J. Aryee and R. A. Irizarry, *Feature selection and dimension
  reduction for single-cell RNA-Seq based on a multinomial model*, Genome Biol. 20 (2019), 295.
* V. Shahrezaei and P. S. Swain, *Analytical distributions for stochastic gene expression*,
  Proc. Natl. Acad. Sci. USA 105 (2008), 17256–17261.
-/

@[expose] public section

open MeasureTheory Real Finset Polynomial
open scoped Nat

namespace ProbabilityTheory

/-- The negative binomial mass function with size `θ` and mean `μ`:
`NB(k; θ, μ) = θ⁽ᵏ⁾ / k! · (θ / (θ + μ)) ^ θ · (μ / (θ + μ)) ^ k`, with the rising factorial
`θ⁽ᵏ⁾ = Γ(θ + k) / Γ(θ)` and a real power `(θ / (θ + μ)) ^ θ`. The parameter domain is `θ > 0`,
`μ ≥ 0`; at `μ = 0` it is the point mass at `0`. Outside the domain the formula is not a
probability mass function. -/
noncomputable def negBinomialReal (θ μ : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval θ / k ! * (θ / (θ + μ)) ^ θ * (μ / (θ + μ)) ^ k

/-- The negative binomial mass function is nonnegative on the parameter domain. -/
theorem negBinomialReal_nonneg {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) (k : ℕ) :
    0 ≤ negBinomialReal θ μ k := by
  have h := ascPochhammer_pos k θ hθ
  unfold negBinomialReal
  positivity

/-- The zero class of the negative binomial law is `(θ / (θ + μ)) ^ θ`. -/
theorem negBinomialReal_zero (θ μ : ℝ) : negBinomialReal θ μ 0 = (θ / (θ + μ)) ^ θ := by
  simp [negBinomialReal]

/-- With mean `0` the negative binomial law is the point mass at `0`. -/
theorem negBinomialReal_mean_zero {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    negBinomialReal θ 0 k = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · simp [negBinomialReal, hθ.ne']
  · simp [negBinomialReal]

/-- **Zero class versus the Poisson law.** For `θ > 0` and `μ ≥ 0`,
`P(0) = (θ / (θ + μ)) ^ θ ≥ e^{-μ}`: a negative binomial law puts at least as much mass at zero
as the Poisson law with the same mean. -/
theorem exp_neg_le_negBinomialReal_zero {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) :
    exp (-μ) ≤ negBinomialReal θ μ 0 := by
  have hpos : 0 < θ / (θ + μ) := div_pos hθ (by linarith)
  rw [negBinomialReal_zero, Real.rpow_def_of_pos hpos, exp_le_exp]
  have h := one_sub_inv_le_log_of_pos hpos
  rw [inv_div] at h
  have h2 : 1 - (θ + μ) / θ = -(μ / θ) := by field_simp; ring
  rw [h2] at h
  have h3 : -μ = θ * (-(μ / θ)) := by field_simp
  rw [h3, mul_comm (log _)]
  exact mul_le_mul_of_nonneg_left h hθ.le

section Gamma

/-- The Poisson mixture over `Gamma(a, b)` in closed form: `a⁽ᵏ⁾ bᵃ / (b + 1)^(a + k) / k!`. -/
private lemma poissonMixtureReal_gammaMeasure_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    poissonMixtureReal (gammaMeasure a b) k =
      (ascPochhammer ℝ k).eval a * b ^ a / (b + 1) ^ (a + k) / k ! := by
  have h := integral_pow_mul_exp_neg_mul_gammaMeasure ha hb zero_le_one k
  simp only [one_mul] at h
  rw [poissonMixtureReal, ← h, ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  simp only
  ring

/-- **Greenwood–Yule.** The Poisson mixture over a Gamma rate of shape `a > 0` and rate `b > 0`
is negative binomial with size `a` and mean `a / b`. -/
theorem poissonMixtureReal_gammaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    poissonMixtureReal (gammaMeasure a b) k = negBinomialReal a (a / b) k := by
  rw [poissonMixtureReal_gammaMeasure_eq ha hb, negBinomialReal]
  have h1 : a / (a + a / b) = b / (b + 1) := by field_simp
  have h2 : a / b / (a + a / b) = 1 / (b + 1) := by field_simp
  have hb1 : 0 < b + 1 := by linarith
  rw [h1, h2, Real.div_rpow hb.le hb1.le, Real.rpow_add hb1, Real.rpow_natCast, div_pow, one_pow]
  have : (b + 1) ^ a ≠ 0 := (Real.rpow_pos_of_pos hb1 a).ne'
  have : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  field_simp

/-- **Greenwood–Yule, mean form.** For `θ, μ > 0`, the Poisson mixture over `Gamma(θ, θ / μ)`
(mean `μ`, variance `μ² / θ`) is `NB(θ, μ)`. -/
theorem poissonMixtureReal_gammaMeasure_mean {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 < μ) (k : ℕ) :
    poissonMixtureReal (gammaMeasure θ (θ / μ)) k = negBinomialReal θ μ k := by
  rw [poissonMixtureReal_gammaMeasure hθ (div_pos hθ hμ), div_div_cancel₀ hθ.ne']

/-- With mean `0` every moment sum `∑ₖ f(k) NB(k; θ, 0)` is `f(0)`. -/
private lemma hasSum_mul_negBinomialReal_mean_zero {θ : ℝ} (hθ : 0 < θ) (f : ℕ → ℝ) :
    HasSum (fun k => f k * negBinomialReal θ 0 k) (f 0) := by
  have h : (fun k => f k * negBinomialReal θ 0 k) = fun k => if k = 0 then f 0 else 0 := by
    funext k
    rw [negBinomialReal_mean_zero hθ]
    split_ifs with hk
    · rw [hk, mul_one]
    · rw [mul_zero]
  rw [h]
  exact hasSum_ite_eq 0 (f 0)

/-- **Normalization.** For `θ > 0` and `μ ≥ 0` the negative binomial masses sum to one. -/
theorem hasSum_negBinomialReal {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) :
    HasSum (negBinomialReal θ μ) 1 := by
  rcases hμ.eq_or_lt with rfl | hμ
  · have h : negBinomialReal θ 0 = fun k => if k = 0 then 1 else 0 :=
      funext (negBinomialReal_mean_zero hθ)
    rw [h]
    exact hasSum_ite_eq 0 1
  · have := isProbabilityMeasure_gammaMeasure hθ (div_pos hθ hμ)
    have h := hasSum_poissonMixtureReal (ae_nonneg_gammaMeasure θ (θ / μ))
    rwa [funext (poissonMixtureReal_gammaMeasure_mean hθ hμ)] at h

/-- **Mean.** For `θ > 0` and `μ ≥ 0` the negative binomial law has mean `μ`. -/
theorem hasSum_mul_negBinomialReal {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ => (k : ℝ) * negBinomialReal θ μ k) μ := by
  rcases hμ.eq_or_lt with rfl | hμ
  · simpa using hasSum_mul_negBinomialReal_mean_zero hθ (fun k => (k : ℝ))
  · have hb := div_pos hθ hμ
    have := isProbabilityMeasure_gammaMeasure hθ hb
    have h := hasSum_mul_poissonMixtureReal (ae_nonneg_gammaMeasure θ (θ / μ))
      (integrable_id_gammaMeasure hθ hb)
    rwa [funext (poissonMixtureReal_gammaMeasure_mean hθ hμ), integral_id_gammaMeasure hθ hb,
      div_div_cancel₀ hθ.ne'] at h

/-- **Second moment.** For `θ > 0` and `μ ≥ 0`, `E N² = μ + μ² / θ + μ²`. -/
theorem hasSum_sq_negBinomialReal {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * negBinomialReal θ μ k) (μ + μ ^ 2 / θ + μ ^ 2) := by
  rcases hμ.eq_or_lt with rfl | hμ
  · have h := hasSum_mul_negBinomialReal_mean_zero hθ (fun k => (k : ℝ) ^ 2)
    simpa using h
  · have hb := div_pos hθ hμ
    have := isProbabilityMeasure_gammaMeasure hθ hb
    have h := hasSum_sq_poissonMixtureReal (ae_nonneg_gammaMeasure θ (θ / μ))
      (integrable_sq_gammaMeasure hθ hb)
    rw [funext (poissonMixtureReal_gammaMeasure_mean hθ hμ), integral_id_gammaMeasure hθ hb,
      integral_sq_gammaMeasure hθ hb] at h
    convert h using 1
    field_simp
    ring

/-- **Variance.** For `θ > 0` and `μ ≥ 0` the negative binomial law has variance
`μ + μ² / θ`. -/
theorem variance_negBinomial {θ μ : ℝ} (hθ : 0 < θ) (hμ : 0 ≤ μ) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * negBinomialReal θ μ k -
        (∑' k : ℕ, (k : ℝ) * negBinomialReal θ μ k) ^ 2 = μ + μ ^ 2 / θ := by
  rw [(hasSum_sq_negBinomialReal hθ hμ).tsum_eq, (hasSum_mul_negBinomialReal hθ hμ).tsum_eq]
  ring

/-- **Gamma–Poisson conjugacy, posterior.** With prior `Λ ~ Gamma(a, b)` (`a, b > 0`) and one
observation `N = k` from `Po(Λ)`, the posterior density (likelihood times prior over the
marginal `NB(k; a, a / b)`) is the `Gamma(a + k, b + 1)` density. -/
theorem gammaPDFReal_posterior {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) (r : ℝ) :
    exp (-r) * r ^ k / k ! * gammaPDFReal a b r / poissonMixtureReal (gammaMeasure a b) k =
      gammaPDFReal (a + k) (b + 1) r := by
  rw [poissonMixtureReal_gammaMeasure_eq ha hb]
  rcases lt_or_ge r 0 with hr | hr
  · simp [gammaPDFReal, not_le.2 hr]
  have hb1 : 0 < b + 1 := by linarith
  have hP := ascPochhammer_pos k a ha
  have hk : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hba : b ^ a ≠ 0 := (Real.rpow_pos_of_pos hb a).ne'
  have hb1a : (b + 1) ^ (a + k) ≠ 0 := (Real.rpow_pos_of_pos hb1 _).ne'
  have hG : Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  simp only [gammaPDFReal, ite_eq_left hr]
  rw [Gamma_add_nat_eq ha, ← pow_mul_rpow_sub_one hr ha k]
  have he : exp (-((b + 1) * r)) = exp (-r) * exp (-(b * r)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  field_simp

/-- **Gamma–Poisson conjugacy, posterior predictive.** With prior `Λ ~ Gamma(a, b)`
(`a, b > 0`) and counts `N, N'` that are independent `Po(Λ)` given `Λ`,
`P(N' = j | N = k) = P(N = k, N' = j) / P(N = k) = NB(j; a + k, (a + k) / (b + 1))`. -/
theorem posterior_predictive_gammaPoisson {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k j : ℕ) :
    (∫ r, exp (-r) * r ^ k / k ! * (exp (-r) * r ^ j / j !) ∂gammaMeasure a b) /
        poissonMixtureReal (gammaMeasure a b) k =
      negBinomialReal (a + k) ((a + k) / (b + 1)) j := by
  have hb1 : 0 < b + 1 := by linarith
  have hb2 : 0 < b + 2 := by linarith
  have hak : 0 < a + k := by positivity
  have hnum : ∫ r, exp (-r) * r ^ k / k ! * (exp (-r) * r ^ j / j !) ∂gammaMeasure a b =
      (ascPochhammer ℝ (k + j)).eval a * b ^ a / (b + 2) ^ (a + (k + j : ℕ)) / (k ! * j !) := by
    have h := integral_pow_mul_exp_neg_mul_gammaMeasure ha hb zero_le_two (k + j)
    rw [← h, ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only
    rw [pow_add, show -(2 * r) = -r + -r by ring, Real.exp_add]
    ring
  rw [hnum, poissonMixtureReal_gammaMeasure_eq ha hb, negBinomialReal]
  have h1 : (a + k) / (a + k + (a + k) / (b + 1)) = (b + 1) / (b + 2) := by
    field_simp; ring
  have h2 : (a + k) / (b + 1) / (a + k + (a + k) / (b + 1)) = 1 / (b + 2) := by
    field_simp; ring
  have hmul : (ascPochhammer ℝ (k + j)).eval a =
      (ascPochhammer ℝ k).eval a * (ascPochhammer ℝ j).eval (a + k) := by
    rw [← ascPochhammer_mul, eval_mul, eval_comp, eval_add, eval_X, eval_natCast]
  rw [h1, h2, hmul, Real.div_rpow hb1.le hb2.le, div_pow, one_pow]
  push_cast
  rw [show a + (k + j : ℝ) = (a + k) + j by ring, Real.rpow_add hb2, Real.rpow_natCast]
  have hP := ascPochhammer_pos k a ha
  have hk : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hj : (j ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
  have hba : b ^ a ≠ 0 := (Real.rpow_pos_of_pos hb a).ne'
  have hb1a : (b + 1) ^ (a + k) ≠ 0 := (Real.rpow_pos_of_pos hb1 _).ne'
  have hb2a : (b + 2) ^ (a + k) ≠ 0 := (Real.rpow_pos_of_pos hb2 _).ne'
  field_simp

end Gamma

section GeneExpression

/-- The net probability flow into state `n` of the immigration–death chain on `ℕ`, in which
molecules are made at rate `κ` (`n → n + 1`) and each decays at rate `γ` (`n → n - 1` at rate
`γ n`): `(κ p(n - 1) + γ (n + 1) p(n + 1)) - (κ + γ n) p(n)`, with no inflow from below at
`n = 0`. A law `p` is stationary (global balance) iff this flow vanishes for every `n`. -/
noncomputable def immigrationDeathFlow (κ γ : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => γ * p 1 - κ * p 0
  | n + 1 => κ * p n + γ * (n + 2) * p (n + 2) - (κ + γ * (n + 1)) * p (n + 1)

/-- **Immigration–death stationary law.** For `γ ≠ 0` the Poisson law with mean `κ / γ`
satisfies global balance for the immigration–death chain. The identity holds for all real `κ`;
the chain is meaningful for `κ ≥ 0`, `γ > 0`. -/
theorem immigrationDeathFlow_poisson {κ γ : ℝ} (hγ : γ ≠ 0) (n : ℕ) :
    immigrationDeathFlow κ γ (fun m => exp (-(κ / γ)) * (κ / γ) ^ m / m !) n = 0 := by
  have hκ : κ = γ * (κ / γ) := by field_simp
  set m := κ / γ
  rcases n with _ | n
  · simp only [immigrationDeathFlow, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
      pow_zero, Nat.factorial_zero, mul_one]
    rw [hκ]
    ring
  · simp only [immigrationDeathFlow]
    rw [hκ, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast
    have hn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp
    ring

/-- **Fano factor of the Poisson law.** For mean `m > 0`, `Var N / E N = 1`; in particular the
stationary law of the immigration–death chain has Fano factor `1`. -/
theorem fano_poisson {m : ℝ} (hm : 0 < m) :
    (∑' k : ℕ, (k : ℝ) ^ 2 * (exp (-m) * m ^ k / k !) -
        (∑' k : ℕ, (k : ℝ) * (exp (-m) * m ^ k / k !)) ^ 2) /
        ∑' k : ℕ, (k : ℝ) * (exp (-m) * m ^ k / k !) = 1 := by
  have hae : (fun _ => m) =ᵐ[Measure.dirac m] id := by
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  have hmem : MemLp id 2 (Measure.dirac m) := (memLp_const m).ae_eq hae
  have h0 : ∀ᵐ r ∂Measure.dirac m, 0 ≤ r := by
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 hm.le
  have hv := variance_poissonMixture h0 hmem
  have he := (hasSum_mul_poissonMixtureReal h0 (hmem.integrable one_le_two)).tsum_eq
  simp only [poissonMixtureReal_dirac, variance_dirac, integral_dirac, add_zero] at hv he
  rw [hv, he, div_self hm.ne']

/-- The net probability flow into state `n` of the bursty production–degradation chain:
bursts arrive at rate `κ` and add `B` molecules, `B` geometric with mean `b`,
`P(B = j) = b ^ j / (1 + b) ^ (j + 1)` for `j ≥ 0`; each molecule decays at rate `γ`. A burst
of size `0` changes nothing, so state `n` is left by a burst at rate `κ P(B ≥ 1) = κ b / (1 + b)`.
The flow is `κ ∑_{m < n} p(m) P(B = n - m) + γ (n + 1) p(n + 1) - (κ b / (1 + b) + γ n) p(n)`. -/
noncomputable def burstDeathFlow (κ γ b : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  κ * ∑ m ∈ range n, p m * (b ^ (n - m) / (1 + b) ^ (n - m + 1)) + γ * (n + 1) * p (n + 1) -
    (κ * (b / (1 + b)) + γ * n) * p n

/-- `n a⁽ⁿ⁾ / n! = a ∑_{m < n} a⁽ᵐ⁾ / m!`. -/
private lemma mul_ascPochhammer_div_eq_sum (a : ℝ) (n : ℕ) :
    (n : ℝ) * ((ascPochhammer ℝ n).eval a / n !) =
      a * ∑ m ∈ range n, (ascPochhammer ℝ m).eval a / m ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih, ascPochhammer_succ_eval, Nat.factorial_succ]
    have hn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    push_cast
    field_simp
    ring

/-- **Bursty expression stationary law** (Shahrezaei–Swain). For burst rate `κ > 0`, decay rate
`γ > 0` and mean burst size `b ≥ 0`, the negative binomial law with size `a = κ / γ` (bursts per
lifetime) and mean `a b` satisfies global balance for the bursty production–degradation
chain. -/
theorem burstDeathFlow_negBinomial {κ γ b : ℝ} (hκ : 0 < κ) (hγ : 0 < γ) (hb : 0 ≤ b) (n : ℕ) :
    burstDeathFlow κ γ b (negBinomialReal (κ / γ) (κ / γ * b)) n = 0 := by
  set a := κ / γ with ha_def
  have ha : 0 < a := div_pos hκ hγ
  have hκa : κ = γ * a := by rw [ha_def]; field_simp
  have hb1 : 0 < 1 + b := by linarith
  have hq : a * b / (a + a * b) = b / (1 + b) := by field_simp
  have hp : a / (a + a * b) = 1 / (1 + b) := by field_simp
  set C := (a / (a + a * b)) ^ a
  set c : ℕ → ℝ := fun m => (ascPochhammer ℝ m).eval a / (m ! : ℝ)
  have hterm : ∀ m ∈ range n, negBinomialReal a (a * b) m * (b ^ (n - m) / (1 + b) ^ (n - m + 1)) =
      C * (b ^ n / (1 + b) ^ (n + 1)) * c m := by
    intro m hm
    have hmn : m ≤ n := (mem_range.1 hm).le
    simp only [negBinomialReal, hq, c, C]
    rw [div_pow, show n = m + (n - m) from (Nat.add_sub_cancel' hmn).symm, Nat.add_sub_cancel_left,
      pow_add, pow_add, pow_succ, pow_succ]
    have : (1 + b) ^ m ≠ 0 := (pow_pos hb1 _).ne'
    have : (1 + b) ^ (n - m) ≠ 0 := (pow_pos hb1 _).ne'
    field_simp
    rw [pow_add]
    ring
  have hS := mul_ascPochhammer_div_eq_sum a n
  have hc1 : c (n + 1) = c n * (a + n) / (n + 1) := by
    simp only [c]
    rw [ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    have hn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp
  have hNB : ∀ m, negBinomialReal a (a * b) m = c m * C * (b / (1 + b)) ^ m := fun m => by
    simp only [negBinomialReal, hq, c, C]
  unfold burstDeathFlow
  rw [sum_congr rfl hterm, ← mul_sum, hNB, hNB, hc1, hκa]
  have hsum : ∑ i ∈ range n, c i = n * c n / a := by
    rw [eq_div_iff ha.ne', mul_comm]
    exact hS.symm
  rw [hsum]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [div_pow, div_pow, pow_succ, pow_succ]
  field_simp
  ring

/-- **Fano factor of bursty expression.** For `a > 0` and `b > 0`, the negative binomial law with
size `a` and mean `a b` has `Var N / E N = 1 + b`. -/
theorem fano_negBinomial {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∑' k : ℕ, (k : ℝ) ^ 2 * negBinomialReal a (a * b) k -
        (∑' k : ℕ, (k : ℝ) * negBinomialReal a (a * b) k) ^ 2) /
        ∑' k : ℕ, (k : ℝ) * negBinomialReal a (a * b) k = 1 + b := by
  have hab : 0 < a * b := mul_pos ha hb
  rw [variance_negBinomial ha hab.le, (hasSum_mul_negBinomialReal ha hab.le).tsum_eq]
  field_simp

end GeneExpression

end ProbabilityTheory
