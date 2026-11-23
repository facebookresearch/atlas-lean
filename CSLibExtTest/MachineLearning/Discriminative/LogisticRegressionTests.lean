/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Discriminative.LogisticRegression

/-!
# Tests for logistic and softmax regression

The log-sum-exp and softmax tests are in `MathlibExtTest/Analysis/SpecialFunctions/`.

* The log-loss of the score `0` is `log 2` for both labels; its derivative at `0` on the label
  `true` is `-1/2`.
* With two classes the cross-entropy of scores `1, 3` is the log-loss of `2`.
* At `0` on `Fin 2`: the cross-entropy of label `0` has gradient `(-1/2, 1/2)`.
* On the examples `e₀` (label `true`) and `e₁` (label `false`) at `w = 0`: the likelihood is
  `1/4`, the risk is `2 log 2`, and its gradient is `(-1/2, 1/2)`.
-/

@[expose] public section

namespace Cslib.MachineLearning.LogisticRegressionTests

open Cslib.MachineLearning LogisticRegression Real

example : logLoss true 0 = log 2 := by
  simp [logLoss, softplus, ind]
  norm_num

example : logLoss false 0 = log 2 := by
  simp [logLoss, softplus, ind]
  norm_num

example : HasDerivAt (logLoss true) (-1 / 2) 0 := by
  convert hasDerivAt_logLoss true 0 using 1
  simp [ind]
  norm_num

example : crossEntropy true (fun c => if c then (3 : ℝ) else 1) = logLoss true 2 := by
  rw [crossEntropy_bool_two]
  norm_num

example : HasFDerivAt (crossEntropy (0 : Fin 2)) (dotL ![-1 / 2, 1 / 2]) 0 := by
  convert hasFDerivAt_crossEntropy (0 : Fin 2) 0 using 2
  funext i
  fin_cases i <;> norm_num [softmax]

/-- Two examples in `ℝ²`. -/
def X2 : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- Their labels. -/
def Y2 : Fin 2 → Bool := ![true, false]

example : likelihood X2 Y2 0 = 1 / 4 := by
  simp [likelihood, X2, Y2, bernoulliDist_weights, unitInterval.coe_sigmoid, sigmoid_def]
  norm_num

example : risk X2 Y2 0 = 2 * log 2 := by
  simp [risk, X2, Y2, logLoss, softplus, ind]
  norm_num

example : HasFDerivAt (risk X2 Y2) (dotL ![-1 / 2, 1 / 2]) 0 := by
  convert hasFDerivAt_risk X2 Y2 0 using 2
  funext i
  fin_cases i <;> simp [X2, Y2, ind, sigmoid_def] <;> norm_num

example (w : Fin 2 → ℝ) : risk X2 Y2 w = -log (likelihood X2 Y2 w) :=
  risk_eq_neg_log_likelihood X2 Y2 w

example : ConvexOn ℝ Set.univ (risk X2 Y2) :=
  convexOn_risk X2 Y2

example : ConvexOn ℝ Set.univ (softmaxRisk X2 Y2) :=
  convexOn_softmaxRisk X2 Y2

example (W : Bool → Fin 2 → ℝ) :
    HasFDerivAt (softmaxRisk X2 Y2)
      (∑ k, (dotL (softmax (scoreMap (X2 k) W) - Pi.single (Y2 k) 1)).comp (scoreMap (X2 k))) W :=
  hasFDerivAt_softmaxRisk X2 Y2 W

end Cslib.MachineLearning.LogisticRegressionTests
