/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Discriminative.ExponentialFamily

/-!
# Tests for exponential families and generalized linear models

* Bernoulli family: the log-partition function is the softplus and the mean the logistic
  function; the density at `η = 0` is `1/2`, the gradient of the log-partition function there is
  `1/2`, and the family is the logistic model's `bernoulliDist`.
* Moment matching on the observations `true, false, true`: the natural parameter `log 2` has mean
  `2/3`, the sample mean, so it maximizes the likelihood.
* GLMs: the Gaussian GLM loss is half the residual sum of squares up to a constant, and on the
  examples `1, 2` with responses `1, 2` its gradient at `0` is `-5`; the Bernoulli (softplus) and
  Poisson (`exp`) GLM losses are convex; logistic regression is the Bernoulli GLM.
-/

@[expose] public section

namespace Cslib.MachineLearning.ExponentialFamilyTests

open Cslib.MachineLearning ExponentialFamily GLM LogisticRegression Real

/-- The Bernoulli base measure. -/
def hB : Bool → ℝ := fun _ => 1

/-- The Bernoulli sufficient statistic. -/
noncomputable def TB : Bool → Unit → ℝ := fun b _ => ind b

example (η : ℝ) : logPartition hB TB (fun _ => η) = softplus η :=
  logPartition_bernoulli η

example (η : ℝ) : mean hB TB (fun _ => η) () = sigmoid η :=
  mean_bernoulli η

example : density hB TB (fun _ => 0) true = 1 / 2 := by
  simp [density, logPartition, hB, TB, ind, dotProduct]
  rw [exp_neg, exp_log two_pos]

example : HasFDerivAt (logPartition hB TB) (dotL fun _ => 1 / 2) (fun _ => 0) := by
  convert hasFDerivAt_logPartition (h := hB) (fun _ => zero_le_one) (by simp [hB]) TB
    (fun _ => 0) using 2
  funext u
  rw [show mean hB TB (fun _ => 0) u = sigmoid 0 from mean_bernoulli 0, sigmoid_def]
  norm_num

example (η : ℝ) : dist (h := hB) (fun _ => zero_le_one) (by simp [hB]) TB (fun _ => η) =
    bernoulliDist (unitInterval.sigmoid η) :=
  dist_bernoulli η

example (η : Unit → ℝ) : ∑ b, density hB TB η b = 1 :=
  sum_density (fun _ => zero_le_one) (by simp) TB η

/-- Observations `true, false, true`. -/
def x3 : Fin 3 → Bool := ![true, false, true]

theorem mean_log_two : (3 : ℝ) • mean hB TB (fun _ => log 2) = ∑ k, TB (x3 k) := by
  funext u
  have h : mean hB TB (fun _ => log 2) u = sigmoid (log 2) := mean_bernoulli (log 2)
  rw [Pi.smul_apply, h, smul_eq_mul, Finset.sum_apply, Fin.sum_univ_three, sigmoid_def, exp_neg,
    exp_log two_pos]
  simp [TB, ind, x3]
  norm_num

/-- **Moment matching**: `log 2` maximizes the likelihood of `true, false, true`. -/
example (η : Unit → ℝ) : likelihood hB TB x3 η ≤ likelihood hB TB x3 (fun _ => log 2) :=
  likelihood_le_of_mean_eq (fun _ => zero_le_one) (by simp) TB x3 mean_log_two η

/-- The iid-likelihood interface of `MathlibExt`: the family on `Bool` with counting measure. -/
example (η : Unit → ℝ) :
    (densityFamily (h := hB) (fun _ => zero_le_one) (by simp [hB]) TB).iidLikelihood 3 η x3 =
      ENNReal.ofReal (likelihood hB TB x3 η) :=
  iidLikelihood_eq _ _ TB x3 η

example : IsMaxOn (fun η => (densityFamily (h := hB) (fun _ => zero_le_one) (by simp [hB])
    TB).iidLikelihood 3 η x3) Set.univ (fun _ => log 2) :=
  isMaxOn_iidLikelihood_of_mean_eq _ _ TB x3 mean_log_two

/-- Two one-dimensional examples. -/
def X2 : Fin 2 → Fin 1 → ℝ := ![![1], ![2]]

example (Y : Fin 2 → ℝ) (θ : Fin 1 → ℝ) :
    glmLoss (fun z => z ^ 2 / 2) X2 Y θ = ∑ k, ((Y k - θ ⬝ᵥ X2 k) ^ 2 - Y k ^ 2) / 2 :=
  glmLoss_sq X2 Y θ

example : HasFDerivAt (glmLoss (fun z => z ^ 2 / 2) X2 ![1, 2]) (dotL ![-5]) 0 := by
  convert hasFDerivAt_glmLoss (A' := id) (fun z => by
    simpa using ((hasDerivAt_id z).pow 2).div_const 2) X2 ![1, 2] 0 using 2
  funext i
  fin_cases i
  simp [X2, Fin.sum_univ_two]
  norm_num

example (Y : Fin 2 → ℝ) : ConvexOn ℝ Set.univ (glmLoss softplus X2 Y) :=
  convexOn_glmLoss convexOn_softplus X2 Y

example (Y : Fin 2 → ℝ) : ConvexOn ℝ Set.univ (glmLoss exp X2 Y) :=
  convexOn_glmLoss convexOn_exp X2 Y

example (Y : Fin 2 → ℝ) (θ v : Fin 1 → ℝ) :
    HasDerivAt (fun t : ℝ => glmLoss exp X2 Y (θ + t • v))
      (∑ k, (exp (θ ⬝ᵥ X2 k) - Y k) * (v ⬝ᵥ X2 k)) 0 :=
  hasDerivAt_glmLoss_line (fun z => hasDerivAt_exp z) X2 Y θ v

example (Y : Fin 2 → Bool) (w : Fin 1 → ℝ) :
    risk X2 Y w = glmLoss softplus X2 (fun k => ind (Y k)) w :=
  risk_eq_glmLoss X2 Y w

end Cslib.MachineLearning.ExponentialFamilyTests
