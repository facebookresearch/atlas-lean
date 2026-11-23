/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.LogSumExp

/-!
# Logistic and softmax regression

Logistic regression models the probability of the label `true` given features `x` as
`sigmoid (w ⬝ᵥ x)`. Its training loss is the log-loss `logLoss y z = log (1 + exp z) - y z` of the
score `z = w ⬝ᵥ x`; softmax regression replaces it by the cross-entropy
`crossEntropy y z = logSumExp z - z y` of a vector of class scores `z c = W c ⬝ᵥ x`.

## Main results

* `logLoss_eq_neg_log`: the log-loss is the negative log-likelihood of the label under the
  Bernoulli distribution with success probability `sigmoid z`; `risk_eq_neg_log_likelihood`: the
  empirical risk is the negative conditional log-likelihood of the data.
* `convexOn_logLoss`, `convexOn_risk`: the log-loss is convex in the score, and the empirical risk
  is convex in the weights `w`.
* `hasDerivAt_logLoss`, `hasFDerivAt_risk`, `hasGradientAt_risk`: the derivative of the log-loss
  is `sigmoid z - y`, so the gradient of the risk is `∑ k, (sigmoid (w ⬝ᵥ x k) - y k) • x k`
  (`hasDerivAt_risk_line` for directional derivatives).
* Softmax regression: `crossEntropy_eq_neg_log_softmax` (the negative log-likelihood of the
  label under the categorical distribution `softmax z`), `convexOn_crossEntropy`,
  `hasFDerivAt_crossEntropy`, `hasGradientAt_crossEntropy` (gradient `softmax z - e_y`),
  `crossEntropy_add_const`, `convexOn_softmaxRisk`, and `hasFDerivAt_softmaxRisk` (the Fréchet
  derivative with respect to the class weights, through the score map `scoreMap`).
* `crossEntropy_bool_two`: with two classes, the cross-entropy of scores `z₀, z₁` is the log-loss
  of `z₁ - z₀`.

The Bernoulli distribution `bernoulliDist p` takes its parameter in Mathlib's `unitInterval`, and
`unitInterval.sigmoid` supplies the logistic model's success probability.

Convexity makes every stationary point a global minimizer; for gradient methods on convex
objectives see `MathlibExt/Analysis/Convex/GradientDescent.lean`.
-/

@[expose] public section

namespace Cslib.MachineLearning.LogisticRegression

open Finset Real

/-- A label as a number: `1` for `true`, `0` for `false`. -/
def ind (y : Bool) : ℝ :=
  if y then 1 else 0

/-- The Bernoulli distribution on `Bool` with success probability `p`. -/
noncomputable def bernoulliDist (p : unitInterval) : Convexity.StdSimplex ℝ Bool :=
  Convexity.StdSimplex.ofWeights (fun b => if b then (p : ℝ) else 1 - p)
    (fun b => by cases b <;> simp [p.2.1, p.2.2]) (by simp)

theorem bernoulliDist_weights (p : unitInterval) (b : Bool) :
    (bernoulliDist p).weights b = if b then (p : ℝ) else 1 - p := by
  simp [bernoulliDist]

/-- The log-loss of the score `z` on the label `y`: `log (1 + exp z) - y z`. -/
noncomputable def logLoss (y : Bool) (z : ℝ) : ℝ :=
  softplus z - ind y * z

/-- **The log-loss is the Bernoulli negative log-likelihood** with success probability
`sigmoid z`. -/
theorem logLoss_eq_neg_log (y : Bool) (z : ℝ) :
    logLoss y z = -log ((bernoulliDist (unitInterval.sigmoid z)).weights y) := by
  rw [bernoulliDist_weights, unitInterval.coe_sigmoid]
  cases y
  · simp only [logLoss, ind, Bool.false_eq_true, ↓reduceIte, zero_mul, sub_zero]
    rw [← sigmoid_neg, neg_log_sigmoid, neg_neg]
  · simp only [logLoss, ind, ↓reduceIte, one_mul]
    rw [neg_log_sigmoid, softplus_neg]

theorem bernoulliDist_sigmoid_pos (z : ℝ) (y : Bool) :
    0 < (bernoulliDist (unitInterval.sigmoid z)).weights y := by
  rw [bernoulliDist_weights, unitInterval.coe_sigmoid]
  cases y
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_pos, sigmoid_lt_one]
  · simp only [↓reduceIte, sigmoid_pos]

/-- The log-loss is convex in the score. -/
theorem convexOn_logLoss (y : Bool) : ConvexOn ℝ Set.univ (logLoss y) := by
  refine ⟨convex_univ, fun x _ x' _ a b ha hb hab => ?_⟩
  have h := convexOn_softplus.2 (Set.mem_univ x) (Set.mem_univ x') ha hb hab
  simp only [logLoss, smul_eq_mul] at h ⊢
  nlinarith

/-- The derivative of the log-loss is `sigmoid z - y`. -/
theorem hasDerivAt_logLoss (y : Bool) (z : ℝ) :
    HasDerivAt (logLoss y) (sigmoid z - ind y) z := by
  have h := (hasDerivAt_softplus z).fun_sub ((hasDerivAt_id z).const_mul (ind y))
  convert h using 1
  · rfl
  · rw [mul_one]

/-! ### The empirical risk -/

variable {ι : Type*} [Fintype ι] {m : ℕ} (X : Fin m → ι → ℝ) (Y : Fin m → Bool)

/-- The empirical risk of the weights `w`: the total log-loss on the data `(X k, Y k)`. -/
noncomputable def risk (w : ι → ℝ) : ℝ :=
  ∑ k, logLoss (Y k) (w ⬝ᵥ X k)

/-- The conditional likelihood of the labels given the features under the logistic model. -/
noncomputable def likelihood (w : ι → ℝ) : ℝ :=
  ∏ k, (bernoulliDist (unitInterval.sigmoid (w ⬝ᵥ X k))).weights (Y k)

/-- **The empirical risk is the negative conditional log-likelihood.** -/
theorem risk_eq_neg_log_likelihood (w : ι → ℝ) : risk X Y w = -log (likelihood X Y w) := by
  rw [risk, likelihood, log_prod fun k _ => (bernoulliDist_sigmoid_pos _ _).ne',
    ← sum_neg_distrib]
  exact sum_congr rfl fun k _ => logLoss_eq_neg_log _ _

/-- **The empirical risk is convex** in the weights. -/
theorem convexOn_risk : ConvexOn ℝ Set.univ (risk X Y) := by
  refine ⟨convex_univ, fun w _ w' _ a b ha hb hab => ?_⟩
  simp only [risk, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  exact (convexOn_logLoss (Y k)).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

/-- **The gradient of the empirical risk** is `∑ k, (sigmoid (w ⬝ᵥ X k) - Y k) • X k`, that is
`Xᵀ (sigmoid (X w) - Y)`. -/
theorem hasFDerivAt_risk (w : ι → ℝ) :
    HasFDerivAt (risk X Y) (dotL (∑ k, (sigmoid (w ⬝ᵥ X k) - ind (Y k)) • X k)) w := by
  have hk : ∀ k, HasFDerivAt (fun w : ι → ℝ => logLoss (Y k) (w ⬝ᵥ X k))
      ((sigmoid (w ⬝ᵥ X k) - ind (Y k)) • dotL (X k)) w := fun k =>
    (hasDerivAt_logLoss (Y k) (w ⬝ᵥ X k)).comp_hasFDerivAt (f := fun w : ι → ℝ => w ⬝ᵥ X k) w
      (hasFDerivAt_dotProduct (X k) w)
  have e : dotL (∑ k, (sigmoid (w ⬝ᵥ X k) - ind (Y k)) • X k) =
      ∑ k, (sigmoid (w ⬝ᵥ X k) - ind (Y k)) • dotL (X k) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [dotProduct_sum, dotProduct_smul]
  rw [e]
  exact HasFDerivAt.fun_sum fun k _ => hk k

/-- The gradient of the empirical risk, in Mathlib's gradient API on `EuclideanSpace ℝ ι`. -/
theorem hasGradientAt_risk (w : ι → ℝ) :
    HasGradientAt (fun u : EuclideanSpace ℝ ι => risk X Y (WithLp.ofLp u))
      (WithLp.toLp 2 (∑ k, (sigmoid (w ⬝ᵥ X k) - ind (Y k)) • X k)) (WithLp.toLp 2 w) :=
  hasGradientAt_ofLp (hasFDerivAt_risk X Y w)

/-- The derivative of the empirical risk at `w` in the direction `v`. -/
theorem hasDerivAt_risk_line (w v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => risk X Y (w + t • v))
      (∑ k, (sigmoid (w ⬝ᵥ X k) - ind (Y k)) * (v ⬝ᵥ X k)) 0 := by
  convert hasDerivAt_line_of_hasFDerivAt (hasFDerivAt_risk X Y w) v using 1
  simp [dotProduct_sum, dotProduct_smul, mul_comm]

/-! ### Softmax regression -/

section Softmax

variable {C : Type*} [Fintype C] [Nonempty C]

/-- The cross-entropy of the class scores `z` on the label `y`: `logSumExp z - z y`. -/
noncomputable def crossEntropy (y : C) (z : C → ℝ) : ℝ :=
  logSumExp z - z y

/-- **The cross-entropy is the categorical negative log-likelihood** under `softmax z`. -/
theorem crossEntropy_eq_neg_log_softmax (y : C) (z : C → ℝ) :
    crossEntropy y z = -log (softmax z y) := by
  rw [log_softmax, crossEntropy, neg_sub]

/-- The cross-entropy is convex in the scores. -/
theorem convexOn_crossEntropy (y : C) : ConvexOn ℝ Set.univ (crossEntropy y) := by
  refine ⟨convex_univ, fun z _ z' _ a b ha hb hab => ?_⟩
  have h := convexOn_logSumExp.2 (Set.mem_univ z) (Set.mem_univ z') ha hb hab
  simp only [crossEntropy, smul_eq_mul, Pi.add_apply, Pi.smul_apply] at h ⊢
  nlinarith

/-- **The gradient of the cross-entropy** is `softmax z` minus the indicator of the label. -/
theorem hasFDerivAt_crossEntropy [DecidableEq C] (y : C) (z : C → ℝ) :
    HasFDerivAt (crossEntropy y) (dotL (softmax z - Pi.single y 1)) z := by
  have e : dotL (softmax z - Pi.single y 1) = dotL (softmax z) - ContinuousLinearMap.proj y := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [dotProduct_sub, dotProduct_single]
  rw [e]
  exact (hasFDerivAt_logSumExp z).sub (hasFDerivAt_apply y z)

/-- The gradient of the cross-entropy, in Mathlib's gradient API on `EuclideanSpace ℝ C`. -/
theorem hasGradientAt_crossEntropy [DecidableEq C] (y : C) (z : C → ℝ) :
    HasGradientAt (fun u : EuclideanSpace ℝ C => crossEntropy y (WithLp.ofLp u))
      (WithLp.toLp 2 (softmax z - Pi.single y 1)) (WithLp.toLp 2 z) :=
  hasGradientAt_ofLp (hasFDerivAt_crossEntropy y z)

/-- The derivative of the cross-entropy in the direction `v` is `∑ c, softmax z c * v c - v y`. -/
theorem hasDerivAt_crossEntropy_line (y : C) (z v : C → ℝ) :
    HasDerivAt (fun t : ℝ => crossEntropy y (z + t • v)) (∑ c, softmax z c * v c - v y) 0 := by
  classical
  convert hasDerivAt_line_of_hasFDerivAt (hasFDerivAt_crossEntropy y z) v using 1
  simp [dotProduct, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_comm]

/-- The cross-entropy is invariant under adding a constant to all scores. -/
theorem crossEntropy_add_const (y : C) (z : C → ℝ) (c : ℝ) :
    crossEntropy y (fun i => z i + c) = crossEntropy y z := by
  rw [crossEntropy, crossEntropy, logSumExp_add_const]
  ring

/-- The empirical risk of softmax regression with class weights `W c`. -/
noncomputable def softmaxRisk (Y : Fin m → C) (W : C → ι → ℝ) : ℝ :=
  ∑ k, crossEntropy (Y k) fun c => W c ⬝ᵥ X k

/-- **The softmax regression risk is convex** in the weights. -/
theorem convexOn_softmaxRisk (Y : Fin m → C) : ConvexOn ℝ Set.univ (softmaxRisk X Y) := by
  refine ⟨convex_univ, fun W _ W' _ a b ha hb hab => ?_⟩
  simp only [softmaxRisk, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  have h := (convexOn_crossEntropy (Y k)).2 (Set.mem_univ fun c => W c ⬝ᵥ X k)
    (Set.mem_univ fun c => W' c ⬝ᵥ X k) ha hb hab
  convert h using 2
  funext c
  simp [add_dotProduct, smul_dotProduct]

/-- The class scores `W ↦ (c ↦ W c ⬝ᵥ x)`, as a continuous linear map. -/
noncomputable def scoreMap (x : ι → ℝ) : (C → ι → ℝ) →L[ℝ] (C → ℝ) :=
  ContinuousLinearMap.pi fun c => (dotL x).comp (ContinuousLinearMap.proj c)

omit [Fintype C] [Nonempty C] in
@[simp]
theorem scoreMap_apply (x : ι → ℝ) (W : C → ι → ℝ) : scoreMap x W = fun c => W c ⬝ᵥ x := by
  funext c
  simp [scoreMap]

/-- **The derivative of the softmax regression risk**: the Fréchet derivative at `W` is
`V ↦ ∑ k, ∑ c, (softmax (scores k) c - [Y k = c]) * (V c ⬝ᵥ X k)`. -/
theorem hasFDerivAt_softmaxRisk [DecidableEq C] (Y : Fin m → C) (W : C → ι → ℝ) :
    HasFDerivAt (softmaxRisk X Y)
      (∑ k, (dotL (softmax (scoreMap (X k) W) - Pi.single (Y k) 1)).comp (scoreMap (X k))) W := by
  have hk : ∀ k, HasFDerivAt (fun W : C → ι → ℝ => crossEntropy (Y k) (scoreMap (X k) W))
      ((dotL (softmax (scoreMap (X k) W) - Pi.single (Y k) 1)).comp (scoreMap (X k))) W :=
    fun k => (hasFDerivAt_crossEntropy (Y k) _).comp W (scoreMap (X k)).hasFDerivAt
  have e : softmaxRisk X Y = fun W => ∑ k, crossEntropy (Y k) (scoreMap (X k) W) := by
    funext W
    simp [softmaxRisk]
  rw [e]
  exact HasFDerivAt.fun_sum fun k _ => hk k

end Softmax

/-- With two classes and scores `0` (for `false`) and `z` (for `true`), the cross-entropy is the
log-loss. -/
theorem crossEntropy_bool (y : Bool) (z : ℝ) :
    crossEntropy y (fun c => if c then z else 0) = logLoss y z := by
  cases y <;> simp [crossEntropy, logSumExp, logLoss, softplus, ind, add_comm]

/-- **Two-class softmax regression is logistic regression**: with scores `z₀` (for `false`) and
`z₁` (for `true`), the cross-entropy is the log-loss of the score difference `z₁ - z₀`. -/
theorem crossEntropy_bool_two (y : Bool) (z₀ z₁ : ℝ) :
    crossEntropy y (fun c => if c then z₁ else z₀) = logLoss y (z₁ - z₀) := by
  rw [← crossEntropy_bool, ← crossEntropy_add_const y (fun c => if c then z₁ - z₀ else 0) z₀]
  congr 1
  funext c
  cases c <;> simp

end Cslib.MachineLearning.LogisticRegression
