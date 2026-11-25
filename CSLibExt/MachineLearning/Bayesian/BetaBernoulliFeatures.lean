/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.BetaBinomial
public import MathlibExt.Probability.IndianBuffet

/-!
# Entry probabilities of the finite beta–Bernoulli feature model

In the finite feature model of Griffiths and Ghahramani (*The Indian buffet process: an
introduction and review*, JMLR 12 (2011), Section 4.1, Equation 9), feature `k` has probability
`πₖ ~ Beta(α/K, 1)` and each entry `zᵢₖ` is a `Bernoulli(πₖ)` trial. This file computes the
probability that an entry is one from the model itself, by integrating the Bernoulli likelihood
(a `Bin(1, πₖ)` trial) against the beta prior, and identifies the closed form `expectedOnes` of
`MathlibExt.Probability.IndianBuffet` (Equation 11) with `N K` times that model probability.

Main results:

* `entry_prob`: `P(zᵢₖ = 1) = (α/K) / (α/K + 1)` in the model.
* `expectedOnes_eq_mul_entry_prob`: `expectedOnes α N K = N K · P(zᵢₖ = 1)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Bayesian.BetaBernoulliFeatures

open MeasureTheory ProbabilityTheory MathlibExt.Probability.IndianBuffet

/-- **Entry probability of the finite feature model.** For `α > 0` and `K ≥ 1` features, an entry
`zᵢₖ` with `πₖ ~ Beta(α/K, 1)` and `zᵢₖ | πₖ ~ Bernoulli(πₖ)` (a single `Bin(1, πₖ)` trial) is
one with probability `(α/K) / (α/K + 1)`, the mean of `Beta(α/K, 1)` (Griffiths and Ghahramani
2011, Section 4.1, Equation 11). -/
theorem entry_prob {α : ℝ} (hα : 0 < α) {K : ℕ} (hK : K ≠ 0) :
    (binomialKernel 1 ∘ₘ betaMeasure (α / K) 1).real {1} = (α / K) / (α / K + 1) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  rw [measureReal_def, binomialKernel_one_comp_betaMeasure (by positivity) one_pos,
    ENNReal.toReal_ofReal (by positivity)]

/-- **The closed-form expected number of ones is `N K` model entry probabilities.** For `α > 0`
and `K ≥ 1`, `expectedOnes α N K = N K · P(zᵢₖ = 1)`, where `P(zᵢₖ = 1)` is computed from the
beta–Bernoulli model. Griffiths and Ghahramani's Equation 11 is the sum of these `N K` equal
entry probabilities, by linearity of expectation; the random matrix itself is not formalized
here. -/
theorem expectedOnes_eq_mul_entry_prob {α : ℝ} (hα : 0 < α) (N : ℕ) {K : ℕ} (hK : K ≠ 0) :
    expectedOnes α N K = N * K * (binomialKernel 1 ∘ₘ betaMeasure (α / K) 1).real {1} := by
  rw [entry_prob hα hK, expectedOnes]

end Cslib.MachineLearning.Bayesian.BetaBernoulliFeatures
