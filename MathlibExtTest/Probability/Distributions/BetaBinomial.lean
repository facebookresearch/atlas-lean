/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BetaBinomial

@[expose] public section

open ProbabilityTheory Polynomial Finset

namespace MathlibExtTest.Probability.Distributions.BetaBinomial

/-- One trial: the beta-binomial law is Bernoulli with success probability `α / (α + β)`. -/
example (α β : ℝ) : betaBinomialPMF 1 α β 1 = α / (α + β) := by
  simp [betaBinomialPMF]

/-- With `α = β = 1` (a uniform success probability) and `n = 2`, every count in `{0, 1, 2}` has
probability `1/3`. -/
example : betaBinomialPMF 2 1 1 0 = 1 / 3 ∧ betaBinomialPMF 2 1 1 1 = 1 / 3 ∧
    betaBinomialPMF 2 1 1 2 = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [betaBinomialPMF, ascPochhammer_succ_eval, Nat.choose]

/-- Boundary: counts above `n` have mass `0`. -/
example (α β : ℝ) : betaBinomialPMF 2 α β 3 = 0 := by
  simp [betaBinomialPMF]

/-- Moments for `n = 4`, `α = 1`, `β = 3`: `π = 1/4`, `γ = 1/5`, so `E M = 1` and
`Var M = 4 · 1/4 · 3/4 · (1 + 3/5) = 6/5`, larger than the binomial variance `3/4`. -/
example :
    ∑ k ∈ range 5, (k : ℝ) * betaBinomialPMF 4 1 3 k = 1 ∧
      ∑ k ∈ range 5, (k : ℝ) ^ 2 * betaBinomialPMF 4 1 3 k -
        (∑ k ∈ range 5, (k : ℝ) * betaBinomialPMF 4 1 3 k) ^ 2 = 6 / 5 := by
  refine ⟨?_, ?_⟩
  · rw [sum_mul_betaBinomialPMF (n := 4) one_pos (by norm_num)]
    norm_num
  · rw [variance_betaBinomial (n := 4) one_pos (by norm_num)]
    norm_num

/-- Normalization on a concrete instance (`n = 3`, `α = 2`, `β = 5`). -/
example : ∑ k ∈ range 4, betaBinomialPMF 3 2 5 k = 1 :=
  sum_betaBinomialPMF (n := 3) (by norm_num) (by norm_num)

/-- Outside the parameter domain the formula is junk: at `α = β = 0` the denominator
`(α + β)⁽¹⁾ = 0`, so Lean's `x / 0 = 0` makes the one-trial masses sum to `0`, not `1`. -/
example : ∑ k ∈ range 2, betaBinomialPMF 1 0 0 k = 0 := by
  simp [betaBinomialPMF]

end MathlibExtTest.Probability.Distributions.BetaBinomial
