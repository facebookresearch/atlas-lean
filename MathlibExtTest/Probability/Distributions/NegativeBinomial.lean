/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.NegativeBinomial

@[expose] public section

open MeasureTheory ProbabilityTheory Real Polynomial Finset
open scoped Nat

namespace MathlibExtTest.Probability.Distributions.NegativeBinomial

/-- With size `θ = 1` the negative binomial law is geometric:
`NB(k; 1, μ) = (1 / (1 + μ)) (μ / (1 + μ)) ^ k`. -/
example (μ : ℝ) (k : ℕ) :
    negBinomialReal 1 μ k = 1 / (1 + μ) * (μ / (1 + μ)) ^ k := by
  simp [negBinomialReal, ascPochhammer_eval_one, Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)]

/-- Concrete masses for `θ = 2`, `μ = 2`: `P(0) = 1/4` and `P(1) = 2 · 1/4 · 1/2 = 1/4`. -/
example : negBinomialReal 2 2 0 = 1 / 4 ∧ negBinomialReal 2 2 1 = 1 / 4 := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [negBinomialReal, ascPochhammer_one, show (2 : ℝ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast]

/-- The mean parametrization is the canonical `p`-parametrization at `p = θ / (θ + μ)`:
`NB(2, 2)` is `negBinomialPMF 2 (1 / 2)`. -/
example (k : ℕ) : negBinomialReal 2 2 k = negBinomialPMF 2 (1 / 2) k := by
  have h := negBinomialReal_eq_negBinomialPMF (θ := 2) (μ := 2) (by norm_num) (by norm_num) k
  have h2 : (2 : ℝ) / (2 + 2) = 1 / 2 := by norm_num
  rw [h2] at h
  exact h

/-- Boundary: mean `0` is the point mass at `0`. -/
example : negBinomialReal 3 0 0 = 1 ∧ negBinomialReal 3 0 5 = 0 := by
  rw [negBinomialReal_mean_zero (by norm_num), negBinomialReal_mean_zero (by norm_num)]
  simp

/-- Outside the parameter domain the formula is junk: with `μ = -1/2 < 0` and `θ = 1` the mass at
`1` is negative. -/
example : negBinomialReal 1 (-1 / 2) 1 < 0 := by
  norm_num [negBinomialReal]

/-- The variance exceeds the mean by `μ² / θ`; with `θ = 2`, `μ = 4` it is `4 + 16 / 2 = 12`. -/
example :
    ∑' k : ℕ, (k : ℝ) ^ 2 * negBinomialReal 2 4 k -
      (∑' k : ℕ, (k : ℝ) * negBinomialReal 2 4 k) ^ 2 = 12 := by
  rw [variance_negBinomial (by norm_num) (by norm_num)]
  norm_num

/-- The zero class of `NB(1, 1)` is `1/2 ≥ e^{-1}`. -/
example : exp (-1) ≤ 1 / 2 := by
  have h := exp_neg_le_negBinomialReal_zero (θ := 1) (μ := 1) one_pos zero_le_one
  rw [negBinomialReal_zero] at h
  norm_num at h
  exact h

/-- Non-vacuity of the Gamma–Poisson theorems: `Gamma(a, b)` with `a, b > 0` is a probability
measure on `[0, ∞)` with square-integrable rate, so the mixed Poisson theorems apply. -/
theorem witness_gamma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (gammaMeasure a b) ∧ (∀ᵐ x ∂gammaMeasure a b, 0 ≤ x) ∧
      Integrable (fun x => x ^ 2) (gammaMeasure a b) := by
  refine ⟨isProbabilityMeasure_gammaMeasure ha hb, ae_nonneg_gammaMeasure a b, ?_⟩
  simpa using integrable_pow_mul_exp_neg_mul_gammaMeasure ha hb le_rfl 2

/-- Greenwood–Yule on a concrete instance: the Poisson mixture over `Gamma(1, 1)` (an
exponential rate) is geometric with `P(k) = 2^{-(k+1)}`. -/
example (k : ℕ) : poissonMixtureReal (gammaMeasure 1 1) k = 1 / 2 * (1 / 2) ^ k := by
  rw [poissonMixtureReal_gammaMeasure one_pos one_pos]
  simp [negBinomialReal, ascPochhammer_eval_one, Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)]
  norm_num

/-- Conjugacy on a concrete instance: after observing `k = 0` under the prior `Gamma(1, 1)`, the
posterior predictive of the next count is `NB(1, 1/2)`, i.e. geometric with
`P(0) = 2/3`. -/
example :
    (∫ r, exp (-r) * r ^ 0 / (0 ! : ℝ) * (exp (-r) * r ^ 0 / (0 ! : ℝ)) ∂gammaMeasure 1 1) /
      poissonMixtureReal (gammaMeasure 1 1) 0 = 2 / 3 := by
  rw [posterior_predictive_gammaPoisson one_pos one_pos 0 0]
  norm_num [negBinomialReal]

/-- The immigration–death chain with `κ = 3`, `γ = 2`: global balance holds in every state. -/
example (n : ℕ) :
    immigrationDeathFlow 3 2 (fun m => exp (-(3 / 2)) * (3 / 2) ^ m / m !) n = 0 :=
  immigrationDeathFlow_poisson (by norm_num) n

/-- The bursty chain with burst rate `2`, decay rate `1` and mean burst size `3`: global balance
holds for `NB(2, 6)`, whose Fano factor is `1 + 3 = 4`. -/
example (n : ℕ) :
    burstDeathFlow 2 1 3 (negBinomialReal 2 6) n = 0 ∧
      (∑' k : ℕ, (k : ℝ) ^ 2 * negBinomialReal 2 6 k -
        (∑' k : ℕ, (k : ℝ) * negBinomialReal 2 6 k) ^ 2) /
        ∑' k : ℕ, (k : ℝ) * negBinomialReal 2 6 k = 4 := by
  refine ⟨?_, ?_⟩
  · have h := burstDeathFlow_negBinomial (κ := 2) (γ := 1) (b := 3) two_pos one_pos
      (by norm_num) n
    norm_num at h
    exact h
  · have h := fano_negBinomial (a := 2) (b := 3) two_pos (by norm_num)
    norm_num at h
    rw [h]

/-- The bursty chain at state `0`, unfolded: with no molecules there is no burst inflow and
`γ P(1) = κ b / (1 + b) P(0)`. -/
example (κ γ b : ℝ) (p : ℕ → ℝ) :
    burstDeathFlow κ γ b p 0 = γ * p 1 - κ * (b / (1 + b)) * p 0 := by
  simp [burstDeathFlow]

end MathlibExtTest.Probability.Distributions.NegativeBinomial
