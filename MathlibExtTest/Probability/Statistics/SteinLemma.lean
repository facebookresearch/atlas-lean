/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SteinLemma

/-!
# Tests for Stein's lemma, SURE and the James–Stein estimator

Stein's lemma for `g = id` (recovering `E[(X - μ) X] = v`) and at the boundary `v = 0`; SURE for
the zero correction (recovering the risk `p` of `X`); the risk of `X` in dimension `0`; the
James–Stein value at the origin (the documented `a / 0 = 0` convention); and the dominance
statement in dimension `3`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.SteinLemma

/-- Stein's lemma with `g = id`: `E[(X - μ) X] = v`. -/
example (μ : ℝ) (v : NNReal) :
    ∫ x, (x - μ) * x ∂gaussianReal μ v = v := by
  have h := (integrable_and_integral_sub_mul_gaussianReal μ v (g := id) (g' := fun _ => 1)
    (fun x => hasDerivAt_id x) (integrable_const 1)).2
  simpa using h

/-- Boundary `v = 0`: the law is the point mass at `μ` and both sides vanish. -/
example (μ : ℝ) {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Integrable g' (gaussianReal μ 0)) :
    ∫ x, (x - μ) * g x ∂gaussianReal μ 0 = 0 := by
  rw [(integrable_and_integral_sub_mul_gaussianReal μ 0 hg hg').2]
  simp

/-- The usual estimator in dimension `0` has risk `0`. -/
example (θ : Fin 0 → ℝ) :
    ∫ x, ∑ i, (x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) = 0 := by
  rw [integral_sum_sq_sub_pi_gaussianReal]
  simp

/-- SURE with the zero correction recovers the risk `p` of `X`. -/
example (θ : Fin 2 → ℝ) :
    ∫ x, ∑ i, (x i + (0 : ℝ) - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) = 2 := by
  have h := integral_sum_sq_add_sub_pi_gaussianReal θ (g := fun _ _ => 0) (dg := fun _ _ => 0)
    (fun _ => Filter.Eventually.of_forall fun _ _ =>
      by simpa using hasDerivAt_const _ (0 : ℝ))
    (fun _ => integrable_const 0) (fun _ => memLp_const 0)
  simpa using h

/-- At the origin the James–Stein estimate is `0` (the factor is `1` by `a / 0 = 0`). -/
example : jamesStein (0 : Fin 3 → ℝ) = 0 := by
  funext i
  simp [jamesStein]

/-- Away from the origin the James–Stein factor is `1 - (p - 2)/‖x‖²`: for `x = (1, 0, 0)` in
dimension `3` the estimate is `0`. -/
example : jamesStein (![1, 0, 0] : Fin 3 → ℝ) = 0 := by
  funext i
  fin_cases i <;> norm_num [jamesStein, Fin.sum_univ_three]

/-- James–Stein dominance in dimension `3` at `θ = 0`. -/
example : ∫ x, ∑ i, (jamesStein x i - 0) ^ 2 ∂(Measure.pi fun _ : Fin 3 => gaussianReal 0 1) <
    3 := by
  have h := integral_jamesStein_risk_lt (le_refl 3) (fun _ => (0 : ℝ))
  rw [integral_sum_sq_sub_pi_gaussianReal] at h
  simpa using h

/-- The mean of `‖X‖⁻²` for `X ~ N(0, I_3)` is `1 / (3 - 2) = 1`. -/
example : ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin 3 => gaussianReal 0 1) = 1 := by
  rw [integral_inv_sum_sq_pi_gaussianReal_zero (le_refl 3)]
  norm_num

/-- The James–Stein factor `(p - 2)/‖z‖²` estimates `1 / V` without bias: `p = 3`, `V = 2`. -/
example : ∫ x, ((3 : ℕ) - 2 : ℝ) / ∑ j, x j ^ 2
    ∂(Measure.pi fun _ : Fin 3 => gaussianReal 0 2) = 1 / 2 := by
  have h := integral_jamesStein_factor_pi_gaussianReal (le_refl 3) (V := 2) two_ne_zero
  simpa using h

/-- The positive-part estimator truncates a negative shrinkage factor: at `x = (1/2, 0, 0)` the
James–Stein factor is `1 - 4 < 0`, so `δ⁺(x) = 0`. -/
example : jamesSteinPlus (![1 / 2, 0, 0] : Fin 3 → ℝ) = 0 := by
  funext i
  fin_cases i <;> norm_num [jamesSteinPlus, Fin.sum_univ_three]

/-- With all coordinates equal, `S = 0` and the grand-mean estimator returns `x`. -/
example : jamesSteinGrandMean 1 (![1, 1, 1, 1] : Fin 4 → ℝ) = ![1, 1, 1, 1] := by
  funext i
  fin_cases i <;> norm_num [jamesSteinGrandMean, Fin.sum_univ_four]

/-- Grand-mean James–Stein dominance in dimension `4` with unit noise at `θ = 0`. -/
example : ∫ x, ∑ i, (jamesSteinGrandMean 1 x i - 0) ^ 2
    ∂(Measure.pi fun _ : Fin 4 => gaussianReal 0 1) < 4 := by
  have h := (integral_jamesSteinGrandMean_risk_lt (le_refl 4) (σ2 := 1) one_ne_zero
    (fun _ => (0 : ℝ))).2
  simpa using h

end MathlibExtTest.Probability.Statistics.SteinLemma
