/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Generative.NaiveBayes

/-!
# Tests for categorical estimates and naive Bayes

* Categorical: the counts `(3, 1)` give the estimate `(3/4, 1/4)`, whose likelihood `27/256`
  exceeds that of the uniform distribution, `1/16`; without observations the estimate is uniform;
  add-one smoothing of `(3, 0)` is `(4/5, 1/5)` and maximizes the posterior kernel.
* Naive Bayes, one binary feature, uniform prior, `P(x = true | true) = 3/4`,
  `P(x = true | false) = 1/4`: the posterior of `true` given `x = true` is `3/4`, and the
  logistic form of the posterior is instantiated.
* Maximum likelihood on three labelled examples of classes `true, true, false` with a third class
  `none` absent (labels in `Option Bool`): the estimated prior of `some true` is `2/3`, and the
  feature distribution of the absent class falls back to uniform.
* Multinomial model: a class without words gets the uniform word distribution.
* The Bayes optimality and maximum likelihood statements are instantiated.
-/

@[expose] public section

namespace Cslib.MachineLearning.NaiveBayesTests

open Cslib.MachineLearning Categorical NaiveBayes Convexity StdSimplex

/-- Counts `3` for `true` and `1` for `false`. -/
def n31 : Bool → ℕ := fun b => if b then 3 else 1

/-- The uniform distribution on `Bool`. -/
noncomputable def half : StdSimplex ℝ Bool :=
  ofWeights (fun _ => 1 / 2) (fun _ => by norm_num) (by simp)

example : (mle n31).weights true = 3 / 4 := by
  rw [mle_apply (by simp [n31])]
  simp [n31]

example : likelihood half n31 = 1 / 16 := by
  simp [likelihood, half, n31]
  norm_num

example : likelihood (mle n31) n31 = 27 / 256 := by
  simp [likelihood, mle_apply (show 0 < ∑ b, n31 b by simp [n31]), n31]
  norm_num

example : likelihood half n31 ≤ likelihood (mle n31) n31 :=
  likelihood_le_mle n31 half

/-- Without observations the estimate is uniform. -/
example : (mle (fun _ : Bool => 0)).weights true = 1 / 2 := by
  rw [mle_of_sum_eq_zero (by simp)]
  simp

example : (laplace (fun b : Bool => if b then 3 else 0)).weights true = 4 / 5 := by
  rw [laplace_apply]
  simp
  norm_num

example : likelihood half (fun b : Bool => if b then 3 else 0) *
      dirichletKernel (fun _ : Bool => (2 : ℝ)) half ≤
    likelihood (laplace fun b : Bool => if b then 3 else 0) (fun b : Bool => if b then 3 else 0) *
      dirichletKernel (fun _ => 2) (laplace fun b : Bool => if b then 3 else 0) :=
  isMaxOn_posterior_laplace _ (Set.mem_univ half)

/-- The distribution on `Bool` putting `3/4` on `b`. -/
noncomputable def skew (b : Bool) : StdSimplex ℝ Bool :=
  ofWeights (fun v => if b = v then 3 / 4 else 1 / 4)
    (fun v => by split_ifs <;> norm_num) (by cases b <;> simp <;> norm_num)

/-- One binary feature, uniform prior. -/
noncomputable def q : Params Bool Unit fun _ => Bool where
  prior := half
  cond c _ := skew c

example : q.posterior (fun _ => true) true = 3 / 4 := by
  simp [Params.posterior, Params.evidence, Params.joint, q, half, skew]
  norm_num

example : q.posterior (fun _ => true) true =
    Real.sigmoid (Params.bernoulliBias q +
      ∑ i, Params.bernoulliWeight q i * if (fun _ : Unit => true) i then 1 else 0) :=
  Params.posterior_true_eq_sigmoid (fun _ => by simp [q, half]) (fun c _ v => by
    simp only [q, skew, ofWeights_weights]; split_ifs <;> norm_num) _

/-- Labels `some true, some true, some false`; the class `none` has no examples. -/
def y3 : Fin 3 → Option Bool := ![some true, some true, some false]

/-- Feature values `true, false, true`. -/
def x3 : Fin 3 → Unit → Bool := ![fun _ => true, fun _ => false, fun _ => true]

example : classCount y3 (some true) = 2 := by decide

example : Params.featCount y3 x3 (some true) () true = 1 := by decide

example : (Params.mle (V := fun _ => Bool) y3 x3).prior.weights (some true) = 2 / 3 := by
  rw [Params.mle_prior_apply y3 x3 (by norm_num), show classCount y3 (some true) = 2 by decide]
  norm_num

example : ((Params.mle y3 x3).cond (some true) ()).weights true = 1 / 2 := by
  rw [Params.mle_cond_apply y3 x3 (by decide), show classCount y3 (some true) = 2 by decide,
    show Params.featCount y3 x3 (some true) () true = 1 by decide]
  norm_num

/-- The class `none` has no examples, so its feature distribution is uniform. -/
example : ((Params.mle y3 x3).cond none ()).weights true = 1 / 2 := by
  simp only [Params.mle]
  rw [mle_of_sum_eq_zero (by decide)]
  simp

example (p : Params (Option Bool) Unit fun _ => Bool) :
    Params.likelihood y3 x3 p ≤ Params.likelihood y3 x3 (Params.mle y3 x3) :=
  Params.likelihood_le_mle y3 x3 p

example (p : Params Bool Unit fun _ => Bool) (h : (Unit → Bool) → Bool) :
    p.risk p.classify ≤ p.risk h :=
  Params.risk_classify_le p h

/-- Two documents of class `true` over the words `Bool`; class `false` has no words. -/
def docs : Fin 2 → Bool → ℕ := ![fun w => if w then 2 else 1, fun _ => 1]

example : ((MultParams.mle (fun _ : Fin 2 => true) docs).word false).weights true = 1 / 2 := by
  simp only [MultParams.mle]
  rw [mle_of_sum_eq_zero (by decide)]
  simp

example {W : Type} [Fintype W] [Nonempty W] (p : MultParams Bool W) (y : Fin 3 → Bool)
    (x : Fin 3 → W → ℕ) :
    MultParams.likelihood y x p ≤ MultParams.likelihood y x (MultParams.mle y x) :=
  MultParams.likelihood_le_mle y x p

end Cslib.MachineLearning.NaiveBayesTests
