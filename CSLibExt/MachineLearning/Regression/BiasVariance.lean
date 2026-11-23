/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance

/-!
# The bias-variance decomposition

At a fixed input, a regression problem has a random response `Y = f + ε` with noise `ε` of mean
zero, and a learned predictor `Ŷ` that is random through its training data, independent of the
new noise. The expected squared prediction error splits as

  `E[(Y - Ŷ)²] = Var ε + (f - E Ŷ)² + Var Ŷ`,

that is, irreducible noise plus squared bias plus variance.

## Main results

* `integral_sq_sub_of_indepFun`: for independent square-integrable `Y` and `Ŷ`,
  `E[(Y - Ŷ)²] = Var Y + Var Ŷ + (E Y - E Ŷ)²`.
* `integral_sq_noise_sub`: the noise + bias² + variance decomposition above.

Without noise (a deterministic target) this is the decomposition of the mean squared error of an
estimator into variance and squared bias, formalized as
`meanSquaredError_eq_variance_add_sq_bias` in
`MathlibExt/Probability/Statistics/EstimationRisk.lean`.
-/

@[expose] public section

namespace Cslib.MachineLearning.BiasVariance

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Expected squared error of independent random variables.** Let $(\Omega, \mu)$ be a
probability space, with expectation $\mathbb{E}$ and variance $\operatorname{Var}$ taken with
respect to $\mu$. If $Y$ and $\hat Y$ are independent square-integrable real random variables on
$\Omega$, then $\mathbb{E}[(Y - \hat Y)^2] = \operatorname{Var}(Y) + \operatorname{Var}(\hat Y) +
(\mathbb{E}[Y] - \mathbb{E}[\hat Y])^2$. -/
theorem integral_sq_sub_of_indepFun {Y Yhat : Ω → ℝ} (hY : MemLp Y 2 μ) (hYhat : MemLp Yhat 2 μ)
    (h : IndepFun Y Yhat μ) :
    μ[(Y - Yhat) ^ 2] = variance Y μ + variance Yhat μ + (μ[Y] - μ[Yhat]) ^ 2 := by
  have hD : MemLp (Y - Yhat) 2 μ := hY.sub hYhat
  have hvar := variance_eq_sub hD
  have hneg : IndepFun Y (-Yhat) μ := h.comp measurable_id measurable_neg
  have hadd := hneg.variance_add hY hYhat.neg
  rw [variance_neg, ← sub_eq_add_neg] at hadd
  have hmean : μ[Y - Yhat] = μ[Y] - μ[Yhat] :=
    integral_sub (hY.integrable one_le_two) (hYhat.integrable one_le_two)
  rw [hmean] at hvar
  linarith

/-- **The bias-variance decomposition.** Let $(\Omega, \mu)$ be a probability space, with
expectation $\mathbb{E}$ and variance $\operatorname{Var}$ taken with respect to $\mu$. Let $f$ be
a real number, and let $\varepsilon$ (the noise) and $\hat Y$ (the predictor) be square-integrable
real random variables on $\Omega$ such that $\mathbb{E}[\varepsilon] = 0$ and $\varepsilon$ is
independent of $\hat Y$. Then the expected squared error of $\hat Y$ for the response
$\varepsilon + f$ is the noise variance plus the squared bias plus the variance of the predictor:
$\mathbb{E}[(\varepsilon + f - \hat Y)^2] = \operatorname{Var}(\varepsilon) +
(f - \mathbb{E}[\hat Y])^2 + \operatorname{Var}(\hat Y)$. -/
theorem integral_sq_noise_sub {ε Yhat : Ω → ℝ} (f : ℝ) (hε : MemLp ε 2 μ) (hε0 : μ[ε] = 0)
    (hYhat : MemLp Yhat 2 μ) (h : IndepFun ε Yhat μ) :
    μ[fun ω => (ε ω + f - Yhat ω) ^ 2] = variance ε μ + (f - μ[Yhat]) ^ 2 + variance Yhat μ := by
  have hY : MemLp (fun ω => ε ω + f) 2 μ := hε.add (memLp_const f)
  have hind : IndepFun (fun ω => ε ω + f) Yhat μ := h.comp (measurable_add_const f) measurable_id
  have key := integral_sq_sub_of_indepFun hY hYhat hind
  rw [variance_add_const hε.aestronglyMeasurable,
    integral_add (hε.integrable one_le_two) (integrable_const f), hε0, integral_const] at key
  simp only [probReal_univ, smul_eq_mul, one_mul, zero_add] at key
  rw [show (fun ω => (ε ω + f - Yhat ω) ^ 2) = ((fun ω => ε ω + f) - Yhat) ^ 2 from rfl, key]
  ring

end Cslib.MachineLearning.BiasVariance
