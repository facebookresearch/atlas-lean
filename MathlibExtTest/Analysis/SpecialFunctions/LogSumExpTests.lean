/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.LogSumExp
import Mathlib.Tactic.FinCases

/-!
# Tests for log-sum-exp, softmax and softplus

* `softmax ![0, 0] = (1/2, 1/2)` (also as the distribution `softmaxDist`), and the logistic
  function of `0` is `1/2` (`softmax_pair`).
* At `0` on `Fin 2`: log-sum-exp is `log 2` with gradient `(1/2, 1/2)`, as a Fréchet derivative
  and in Mathlib's `HasGradientAt` API.
* `softplus (-1) = softplus 1 - 1` and `-log (sigmoid 0) = softplus 0`.
* `unitInterval.sigmoid 0` is `1/2` as a real number.
-/

namespace MathlibExtTest.LogSumExp

open Real

example : softmax ![(0 : ℝ), 0] 1 = 1 / 2 := by
  simp [softmax, Fin.sum_univ_two]
  norm_num

example : (softmaxDist ![(0 : ℝ), 0]).weights 0 = 1 / 2 := by
  rw [softmaxDist_weights]
  simp [softmax, Fin.sum_univ_two]
  norm_num

/-- The gradient of log-sum-exp at `0` in Mathlib's gradient API. -/
example : HasGradientAt (fun w : EuclideanSpace ℝ (Fin 2) => logSumExp (WithLp.ofLp w))
    (WithLp.toLp 2 (softmax 0)) (WithLp.toLp 2 0) :=
  hasGradientAt_logSumExp 0

example : softmax ![(0 : ℝ), 0] 1 = sigmoid 0 := by
  rw [softmax_pair, sub_zero]

example : logSumExp (0 : Fin 2 → ℝ) = log 2 := by
  simp [logSumExp]

example : HasFDerivAt logSumExp (dotL ![1 / 2, 1 / 2]) (0 : Fin 2 → ℝ) := by
  convert hasFDerivAt_logSumExp (0 : Fin 2 → ℝ) using 2
  funext i
  fin_cases i <;> simp [softmax]

example : softplus (-1) = softplus 1 - 1 :=
  softplus_neg 1

example : -log (sigmoid 0) = softplus 0 := by
  rw [neg_log_sigmoid, neg_zero]

example : (unitInterval.sigmoid 0 : ℝ) = 1 / 2 := by
  rw [unitInterval.coe_sigmoid, sigmoid_zero]
  norm_num

end MathlibExtTest.LogSumExp
