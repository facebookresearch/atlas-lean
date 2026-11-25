/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Robbins' formula for Poisson empirical Bayes

Let a rate `θ ≥ 0` be drawn from a prior `g` and, given `θ`, let `x` be Poisson with mean `θ`.
Write `f(x) = ∫ e^{-θ} θ^x / x! g(dθ)` for the marginal mass of `x` (its marginal probability
when `g` is a probability measure). Bayes' rule gives the
posterior mean `E[θ | x] = ∫ θ e^{-θ} θ^x / x! g(dθ) / f(x)`, and **Robbins' formula** says that
it equals `(x + 1) f(x + 1) / f(x)`: like Tweedie's formula in the Gaussian case, it expresses a
Bayes rule through the marginal law alone, which empirical Bayes estimates from the counts
(B. Efron, *Empirical Bayes: Concepts and Methods*, 2021 manuscript, equation (1.7); Robbins
1956).

## Main results

* `poissonMixtureMass`, `poissonPosteriorMean`: the marginal mass and the posterior mean.
* `poissonPosteriorMean_eq`: Robbins' formula.

## References

* H. Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math.
  Statist. Probab., Vol. 1, Univ. California Press (1956), 157–163.
* B. Efron, *Empirical Bayes: Concepts and Methods*, manuscript (2021), equations (1.1)–(1.7).
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

/-- **Marginal mass of a Poisson mixture.** For a prior `g` on the rate, the Bochner integral
`f(x) = ∫ e^{-θ} θ^x / x! g(dθ)`. When `θ ↦ e^{-θ} θ^x / x!` is `g`-integrable (for instance for
every finite prior) it is the marginal mass of the count `x`: the probability of `x` when
`θ ~ g` and `x | θ ~ Poisson(θ)` if `g` is a probability measure, and the unnormalised marginal
mass otherwise (for example `10 / e > 1` for `g = 10 δ₁`). When the integrand is not integrable
the Bochner integral is `0`, which is not the marginal mass: for `g = ∞ • δ₁` the value is `0`,
although `∫⁻ θ, Poisson(θ){x} ∂g = ∞`. -/
noncomputable def poissonMixtureMass (g : Measure ℝ≥0) (x : ℕ) : ℝ :=
  ∫ θ, (poissonMeasure θ).real {x} ∂g

/-- **Posterior mean in the Poisson model.** Bayes' rule for `θ ~ g` and `x | θ ~ Poisson(θ)`:
`E[θ | x] = ∫ θ e^{-θ} θ^x / x! g(dθ) / f(x)`, with `f` the marginal mass. It is the posterior
mean when both integrands are `g`-integrable and the normaliser is positive and finite,
`0 < f(x) < ∞`, which covers every finite prior with `f(x) > 0`. Otherwise the Bochner integrals
are totalised and the value is `0` (for example for `g = ∞ • δ₁`), not a posterior mean. -/
noncomputable def poissonPosteriorMean (g : Measure ℝ≥0) (x : ℕ) : ℝ :=
  (∫ θ, (θ : ℝ) * (poissonMeasure θ).real {x} ∂g) / poissonMixtureMass g x

/-- **Robbins' formula.** For every prior `g` on the Poisson rate and every count `x`, the posterior
mean is `E[θ | x] = (x + 1) f(x + 1) / f(x)`, where `f` is the marginal mass (Efron, 2021
manuscript, equation (1.7); Robbins 1956). As an identity between the totalised quantities
above it holds for any measure `g`, with no moment assumption: it rests on
`θ e^{-θ} θ^x / x! = (x + 1) e^{-θ} θ^{x+1} / (x + 1)!`. It is Robbins' formula for the posterior
mean wherever `poissonPosteriorMean` is one (integrable integrands, positive finite marginal). -/
theorem poissonPosteriorMean_eq (g : Measure ℝ≥0) (x : ℕ) :
    poissonPosteriorMean g x =
      (x + 1) * poissonMixtureMass g (x + 1) / poissonMixtureMass g x := by
  rw [poissonPosteriorMean, poissonMixtureMass, poissonMixtureMass, ← integral_const_mul]
  congr 2
  ext θ
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end ProbabilityTheory
