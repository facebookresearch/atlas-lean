/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Deriv
import MathlibExt.Analysis.Convex.FinsetSum
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Logistic regression and support vector machines are convex problems

Two standard classifiers are trained by minimizing convex functions of the parameters, so their
training problems are convex optimization problems (and the methods of convex optimization, e.g.
gradient descent or interior-point methods, apply).

* **Logistic regression.** With design matrix `X` (one row `xₖ` per example) and labels
  `yₖ ∈ {0, 1}`, the logistic model gives `P(yₖ = 1) = σ(xₖᵀ θ)` with the sigmoid
  `σ(z) = exp z / (1 + exp z)`. The negative log-likelihood is
  `logisticNLL X y θ = ∑ₖ (log (1 + exp zₖ) - yₖ zₖ)` with `z = X θ`
  (`logisticNLL_eq_neg_logLikelihood`), and it is convex in `θ` (`convexOn_logisticNLL`), from the
  convexity of the softplus function `t ↦ log (1 + exp t)` (`convexOn_log_one_add_exp`), whose
  derivative is the sigmoid.
* **Support vector machine.** With labels `yₖ ∈ {-1, 1}`, the soft-margin SVM minimizes the hinge
  loss plus a ridge penalty, `∑ₖ max 0 (1 - yₖ (xₖᵀ w + b)) + λ ‖w‖²`, which is convex in `(w, b)`
  for `λ ≥ 0` (`convexOn_svmObjective`). The hinge loss is a convex upper bound on the number of
  misclassified examples (`card_misclassified_le_sum_hinge`), the "convex relaxation" of
  Boyd–Vandenberghe §8.6.1.

## Relation to `MathlibExt.Probability.Statistics.LogisticRegression`

That module defines the same loss (its `logisticNLL`, design matrix `Fin n → Fin m → ℝ`), proves
its `convexOn_logisticNLL` from `Real.convexOn_softplus` (the statement of
`convexOn_log_one_add_exp`) and adds gradient and descent-rate results, but has no SVM part.
`hasDerivAt_log_one_add_exp` is also in `MathlibExt.Probability.Statistics.GLM.Canonical`.

## References

* S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, §7.1.1
  (logistic regression, eq. (7.3)) and §8.6.1 (support vector classifier).
* T. Hastie, R. Tibshirani and J. Friedman, *The Elements of Statistical Learning*, 2nd ed.,
  Springer, 2009, §4.4 (logistic regression) and §12.3.2 (the SVM as a penalization method:
  hinge loss plus ridge penalty).
-/

@[expose] public section

namespace Cslib.MachineLearning.LogisticSVM

open Real Matrix Finset MathlibExt.Analysis.Convex.FinsetSum

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- The softplus function `t ↦ log (1 + exp t)` has derivative the sigmoid
`σ(t) = 1 / (1 + exp (-t))`. -/
theorem hasDerivAt_log_one_add_exp (t : ℝ) :
    HasDerivAt (fun s => Real.log (1 + Real.exp s)) (Real.sigmoid t) t := by
  have hpos : 0 < 1 + Real.exp t := by positivity
  have h := ((Real.hasDerivAt_exp t).const_add 1).log hpos.ne'
  convert h using 1
  rw [Real.sigmoid_def, Real.exp_neg]
  field_simp
  ring

/-- **Convexity of the softplus function** `t ↦ log (1 + exp t)`: its derivative, the sigmoid, is
monotone.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.5 (log-sum-exp is convex; `log (1 + exp t) = log (exp 0 + exp t)`) and §7.1.1. -/
theorem convexOn_log_one_add_exp :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (1 + Real.exp t)) := by
  have hd : ∀ t, HasDerivAt (fun s => Real.log (1 + Real.exp s)) (Real.sigmoid t) t :=
    hasDerivAt_log_one_add_exp
  have hderiv : deriv (fun s => Real.log (1 + Real.exp s)) = Real.sigmoid :=
    funext fun t => (hd t).deriv
  refine Monotone.convexOn_univ_of_deriv (fun t => (hd t).differentiableAt) ?_
  rw [hderiv]
  exact Real.sigmoid_monotone

/-- The **negative log-likelihood of logistic regression**,
`∑ₖ (log (1 + exp zₖ) - yₖ zₖ)` with linear predictor `z = X θ`. It equals
`-∑ₖ (yₖ log σ(zₖ) + (1 - yₖ) log (1 - σ(zₖ)))` for all real `y`
(`logisticNLL_eq_neg_logLikelihood`), which for labels `yₖ ∈ {0, 1}` is minus the log-likelihood.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§7.1.1 (the log-likelihood `l(a, b)` of the logistic model (7.3), with the intercept `b` folded
into `θ` as a constant column of `X`). -/
noncomputable def logisticNLL (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (θ : ι → ℝ) : ℝ :=
  ∑ k, (Real.log (1 + Real.exp ((X *ᵥ θ) k)) - y k * (X *ᵥ θ) k)

/-- **The logistic loss is the negative log-likelihood of the logistic model.** With
`pₖ = σ((X θ)ₖ) = exp zₖ / (1 + exp zₖ)` the modelled probability that `yₖ = 1`,
`logisticNLL X y θ = -∑ₖ (yₖ log pₖ + (1 - yₖ) log (1 - pₖ))`; for `yₖ ∈ {0, 1}` the right side
is minus the log-likelihood of the observed labels.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§7.1.1, eq. (7.3) and the log-likelihood that follows it. -/
theorem logisticNLL_eq_neg_logLikelihood (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ)
    (θ : ι → ℝ) :
    logisticNLL X y θ = -∑ k, (y k * Real.log (Real.sigmoid ((X *ᵥ θ) k)) +
      (1 - y k) * Real.log (1 - Real.sigmoid ((X *ᵥ θ) k))) := by
  unfold logisticNLL
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  set z := (X *ᵥ θ) k
  have hpos : 0 < 1 + Real.exp z := by positivity
  have h1 : Real.sigmoid z = Real.exp z / (1 + Real.exp z) := by
    rw [Real.sigmoid_def, Real.exp_neg]
    field_simp
    ring
  have h2 : 1 - Real.sigmoid z = (1 + Real.exp z)⁻¹ := by
    rw [h1]
    field_simp
    ring
  rw [h2, h1, Real.log_div (Real.exp_pos z).ne' hpos.ne', Real.log_exp, Real.log_inv]
  ring

/-- **Logistic regression is a convex problem**: the negative log-likelihood `logisticNLL X y` is
convex in `θ`, for any real labels `y`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§7.1.1 ("Since `l` is a concave function of `a` and `b`, the logistic regression problem can be
solved as a convex optimization problem"). -/
theorem convexOn_logisticNLL (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (logisticNLL X y) := by
  unfold logisticNLL
  refine convexOn_finset_sum convex_univ _ fun k _ => ?_
  let L : (ι → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj k).comp X.mulVecLin
  have hL : ∀ θ, L θ = (X *ᵥ θ) k := fun θ => rfl
  have h1 : ConvexOn ℝ Set.univ (fun θ : ι → ℝ => Real.log (1 + Real.exp ((X *ᵥ θ) k))) := by
    have := convexOn_log_one_add_exp.comp_linearMap L
    simpa [Function.comp_def, hL] using this
  have h2 : ConvexOn ℝ Set.univ (fun θ : ι → ℝ => -(y k * (X *ᵥ θ) k)) := by
    exact (((-(y k)) • L).convexOn convex_univ).congr fun θ _ => by
      simp only [LinearMap.smul_apply, hL, smul_eq_mul, neg_mul]
  exact (h1.add h2).congr fun θ _ => by simp only [Pi.add_apply]; ring

/-- The **soft-margin support vector machine objective**
`∑ₖ max 0 (1 - yₖ (xₖᵀ w + b)) + λ w ⬝ w`: the hinge loss of the affine classifier
`x ↦ xᵀ w + b` plus a ridge penalty on `w` (the intercept `b` is not penalized).

Source: T. Hastie, R. Tibshirani and J. Friedman, *The Elements of Statistical Learning*, 2nd ed.,
Springer, 2009, §12.3.2 ("The SVM as a Penalization Method"); S. Boyd and L. Vandenberghe,
*Convex Optimization*, Cambridge University Press, 2004, §8.6.1 (the support vector classifier,
in slack-variable form). -/
noncomputable def svmObjective (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (lam : ℝ) (w : ι → ℝ)
    (b : ℝ) : ℝ :=
  ∑ k, max 0 (1 - y k * ((X *ᵥ w) k + b)) + lam * (w ⬝ᵥ w)

/-- **The support vector machine is a convex problem**: for `λ ≥ 0`, the SVM objective is convex
in `(w, b)`.

Source: T. Hastie, R. Tibshirani and J. Friedman, *The Elements of Statistical Learning*, 2nd ed.,
Springer, 2009, §12.3.2; S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University
Press, 2004, §8.6.1. -/
theorem convexOn_svmObjective (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    ConvexOn ℝ Set.univ (fun p : (ι → ℝ) × ℝ => svmObjective X y lam p.1 p.2) := by
  unfold svmObjective
  refine ConvexOn.add (convexOn_finset_sum convex_univ _ fun k _ => ?_) ?_
  · let L : ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj k).comp (X.mulVecLin.comp (LinearMap.fst ℝ (ι → ℝ) ℝ)) +
        LinearMap.snd ℝ (ι → ℝ) ℝ
    have hL : ∀ p : (ι → ℝ) × ℝ, L p = (X *ᵥ p.1) k + p.2 := fun p => rfl
    have haff : ConvexOn ℝ Set.univ
        (fun p : (ι → ℝ) × ℝ => 1 - y k * ((X *ᵥ p.1) k + p.2)) := by
      refine ((convexOn_const (1 : ℝ) convex_univ).add
        (((-(y k)) • L).convexOn convex_univ)).congr fun p _ => ?_
      simp only [Pi.add_apply, LinearMap.smul_apply, hL, smul_eq_mul]
      ring
    exact (convexOn_const 0 convex_univ).sup haff
  · have hsq : ConvexOn ℝ Set.univ (fun p : (ι → ℝ) × ℝ => p.1 ⬝ᵥ p.1) := by
      simp only [dotProduct]
      refine convexOn_finset_sum convex_univ _ fun i _ => ?_
      have hpow : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) :=
        (show Even 2 by norm_num).convexOn_pow
      let P : ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp (LinearMap.fst ℝ (ι → ℝ) ℝ)
      have := hpow.comp_linearMap P
      simpa [Function.comp_def, P, sq] using this
    simpa [smul_eq_mul] using hsq.smul hlam

/-- **The hinge loss bounds the number of misclassified examples.** The number of examples on the
wrong side of, or on, the decision boundary (`yₖ (xₖᵀ w + b) ≤ 0`) is at most the total hinge
loss `∑ₖ max 0 (1 - yₖ (xₖᵀ w + b))`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§8.6.1 (the slack sum "is a convex relaxation for the number of misclassified points"). -/
theorem card_misclassified_le_sum_hinge (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (w : ι → ℝ)
    (b : ℝ) :
    ((Finset.univ.filter fun k => y k * ((X *ᵥ w) k + b) ≤ 0).card : ℝ) ≤
      ∑ k, max 0 (1 - y k * ((X *ᵥ w) k + b)) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  split_ifs with h
  · simp only [Nat.cast_one]
    exact le_max_of_le_right (by linarith)
  · simp

end Cslib.MachineLearning.LogisticSVM
