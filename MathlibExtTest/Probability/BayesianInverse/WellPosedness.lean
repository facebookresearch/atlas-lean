/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BayesianInverse.WellPosedness
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.HellingerDistance MathlibExt.Probability.BayesianInverse

namespace MathlibExtTest.Probability.BayesianInverse.WellPosedness

/-- Non-degenerate instance of well-posedness: standard Gaussian prior on `ℝ`, nonlinear
forward map `G = sin`, unit Gaussian noise, misfit `Φ(u; y) = (y - sin u)² / 2`. Here
`M₁ = 0` and `M₂ = r + 1`. -/
example (r : ℝ) : ∃ C, ∀ y y' : ℝ, ‖y‖ ≤ r → ‖y'‖ ≤ r →
    hellingerDist (posterior (gaussianReal 0 1) fun u ↦ (y - Real.sin u) ^ 2 / 2)
      (posterior (gaussianReal 0 1) fun u ↦ (y' - Real.sin u) ^ 2 / 2) ≤ C * ‖y - y'‖ := by
  refine hellingerDist_posterior_le_mul_dist (gaussianReal 0 1)
    (fun u y ↦ (y - Real.sin u) ^ 2 / 2) (fun _ ↦ 0) (fun _ ↦ r + 1) r
    (fun y ↦ by fun_prop) monotone_const monotone_const
    (fun u y _ ↦ by simp only [neg_zero]; positivity) ?_ (integrable_const _)
  intro u y y' hy hy'
  rw [Real.norm_eq_abs] at hy hy' ⊢
  have hs := Real.abs_sin_le_one u
  have hfac : (y - Real.sin u) ^ 2 / 2 - (y' - Real.sin u) ^ 2 / 2 =
      (y - y') * ((y + y') / 2 - Real.sin u) := by ring
  rw [hfac, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_le] at hy hy' hs ⊢
  constructor <;> linarith [hy.1, hy.2, hy'.1, hy'.2, hs.1, hs.2]

/-- Normalising constants of that example are uniformly positive on bounded data sets. -/
example (r : ℝ) (hr : 0 ≤ r) : ∃ z > 0, ∀ y : ℝ, ‖y‖ ≤ r →
    z ≤ normalizer (gaussianReal 0 1) fun u ↦ (y - Real.sin u) ^ 2 / 2 := by
  refine exists_pos_le_normalizer (gaussianReal 0 1) (fun u y ↦ (y - Real.sin u) ^ 2 / 2)
    (fun _ ↦ 0) (fun _ ↦ r + 1) hr (fun y ↦ by fun_prop) monotone_const ?_
    (fun u y _ ↦ by simp only [neg_zero]; positivity) (integrable_const _)
  intro u y y' hy hy'
  rw [Real.norm_eq_abs] at hy hy' ⊢
  have hs := Real.abs_sin_le_one u
  have hfac : (y - Real.sin u) ^ 2 / 2 - (y' - Real.sin u) ^ 2 / 2 =
      (y - y') * ((y + y') / 2 - Real.sin u) := by ring
  rw [hfac, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_le] at hy hy' hs ⊢
  constructor <;> linarith [hy.1, hy.2, hy'.1, hy'.2, hs.1, hs.2]

/-- Non-degenerate instance of the approximation theorem: the forward model `G = sin` is
replaced by `Gᴺ = sin + 1/(N+1)`, which changes the posterior, with `M₁ = 0`, `M₂ = |y| + 2` and
`ψ(N) = 1/(N+1)`. -/
example (y : ℝ) : ∃ C, ∀ᶠ N : ℕ in atTop,
    hellingerDist (posterior (gaussianReal 0 1) fun u ↦ (y - Real.sin u) ^ 2 / 2)
      (posterior (gaussianReal 0 1) fun u ↦ (y - Real.sin u - 1 / ((N : ℝ) + 1)) ^ 2 / 2) ≤
        C * |1 / ((N : ℝ) + 1)| := by
  refine hellingerDist_posterior_approx_le (gaussianReal 0 1)
    (fun u ↦ (y - Real.sin u) ^ 2 / 2) (fun N u ↦ (y - Real.sin u - 1 / ((N : ℝ) + 1)) ^ 2 / 2)
    (fun N ↦ 1 / ((N : ℝ) + 1)) (fun _ ↦ 0) (fun _ ↦ |y| + 2) (by fun_prop)
    (fun N ↦ by fun_prop) monotone_const monotone_const
    (fun u ↦ by simp only [neg_zero]; positivity) (fun N u ↦ by simp only [neg_zero]; positivity)
    (fun N u ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat (integrable_const _)
  set ε : ℝ := 1 / ((N : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hfac : (y - Real.sin u) ^ 2 / 2 - (y - Real.sin u - ε) ^ 2 / 2 =
      ε * (y - Real.sin u - ε / 2) := by ring
  rw [hfac, abs_mul, abs_of_pos hε0, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hε0.le
  have hs := abs_le.1 (Real.abs_sin_le_one u)
  rw [abs_le]
  constructor <;> linarith [neg_abs_le y, le_abs_self y, hs.1, hs.2]

end MathlibExtTest.Probability.BayesianInverse.WellPosedness
