/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MonotoneLikelihoodRatio
import Mathlib.Tactic.NormNum

/-!
# Tests for monotone likelihood ratio and posterior ordering

Concrete Poisson and binomial likelihood values, the MLR instances for the identity mean and
the identity success probability, posterior ordering under a two-point prior (non-vacuity of
the hypotheses), and the junk value of `posteriorTail` under the zero prior.
-/

@[expose] public section

open MeasureTheory Set Real ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.MonotoneLikelihoodRatio

/-- The Poisson likelihood of `0` under mean `2` is `e^{-2}`. -/
example (θ : ℝ) : poissonLik (fun _ => 2) 0 θ = exp (-2) := by
  simp [poissonLik]

/-- The binomial likelihood of one success in two fair trials is `1/2`. -/
example (θ : ℝ) : binomialLik 2 (fun _ => 1 / 2) 1 θ = 1 / 2 := by
  norm_num [binomialLik]

/-- The binomial likelihood vanishes above the number of trials. -/
example (θ : ℝ) : binomialLik 2 (fun _ => 1 / 2) 3 θ = 0 := by
  simp [binomialLik]

/-- The Poisson family with mean `θ` has a monotone likelihood ratio on `(0, ∞)`. -/
example : HasMonotoneLikelihoodRatioOn (poissonLik id) (Ioi 0) :=
  poissonLik_hasMLR monotoneOn_id fun _ h => le_of_lt h

/-- The Poisson family with mean `1/θ` has an antitone likelihood ratio on `(0, ∞)`. -/
example : HasAntitoneLikelihoodRatioOn (poissonLik fun θ => 1 / θ) (Ioi 0) :=
  poissonLik_hasAntitoneLR (fun _ ha _ _ hab => one_div_le_one_div_of_le ha hab)
    fun _ h => le_of_lt (one_div_pos.mpr h)

/-- The binomial family with success probability `θ` has a monotone likelihood ratio on
`[0, 1]`. -/
example (N : ℕ) : HasMonotoneLikelihoodRatioOn (binomialLik N id) (Icc 0 1) :=
  binomialLik_hasMLR monotoneOn_id fun _ h => h

/-- Under any prior with integrable likelihoods, the MLR ordering holds (here instantiated for
the binomial family on `[0, 1]`). -/
example {μ : Measure ℝ} (hμ : μ (Icc 0 1)ᶜ = 0)
    (hint : ∀ n, Integrable (binomialLik 3 id n) μ) (t : ℝ) :
    (∫ θ in Ioi t, binomialLik 3 id 1 θ ∂μ) * ∫ θ, binomialLik 3 id 2 θ ∂μ ≤
      (∫ θ in Ioi t, binomialLik 3 id 2 θ ∂μ) * ∫ θ, binomialLik 3 id 1 θ ∂μ :=
  setIntegral_Ioi_mul_integral_le_of_hasMLR hμ
    (binomialLik_hasMLR monotoneOn_id fun _ h => h) hint (by norm_num) t

/-- Junk value: under the zero prior the marginal likelihood is `0` and `posteriorTail` returns
`0`; the posterior theorems require positive marginal likelihoods. -/
example (L : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : posteriorTail 0 L n t = 0 := by
  simp [posteriorTail]

end MathlibExtTest.Probability.Statistics.MonotoneLikelihoodRatio
