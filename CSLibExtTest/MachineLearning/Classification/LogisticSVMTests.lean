/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Classification.LogisticSVM

/-!
# Tests for logistic regression and the support vector machine

* The softplus function has slope `σ(0) = 1/2` at `0`.
* One example with feature `1`, label `1` and `θ = 0`: the logistic loss is `log 2`, i.e. minus
  the log-likelihood `log (1/2)` of the label under `P(y = 1) = σ(0) = 1/2`.
* Convexity of the logistic loss and of the SVM objective, used through Jensen's midpoint
  inequality.
* A misclassified point (feature `1`, label `-1`, classifier `w = 1`, `b = 0`) counts once, and the
  hinge loss `2` bounds the count.
-/

namespace Cslib.MachineLearning.LogisticSVM

open Matrix

example : HasDerivAt (fun s => Real.log (1 + Real.exp s)) (1 / 2) 0 := by
  simpa [Real.sigmoid_zero] using hasDerivAt_log_one_add_exp 0

example : logisticNLL (m := 1) (ι := Fin 1) !![1] ![1] ![0] = Real.log 2 := by
  simp [logisticNLL, mulVec, dotProduct]
  norm_num

example : logisticNLL (m := 1) (ι := Fin 1) !![1] ![1] ![0] =
    -Real.log (Real.sigmoid 0) := by
  rw [logisticNLL_eq_neg_logLikelihood]
  simp [mulVec, dotProduct]

example (X : Matrix (Fin 3) (Fin 2) ℝ) (y : Fin 3 → ℝ) (θ θ' : Fin 2 → ℝ) :
    logisticNLL X y ((1 / 2 : ℝ) • θ + (1 / 2 : ℝ) • θ') ≤
      (1 / 2 : ℝ) * logisticNLL X y θ + (1 / 2 : ℝ) * logisticNLL X y θ' := by
  have := (convexOn_logisticNLL X y).2 (Set.mem_univ θ) (Set.mem_univ θ')
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa [smul_eq_mul] using this

example (X : Matrix (Fin 3) (Fin 2) ℝ) (y : Fin 3 → ℝ) (w w' : Fin 2 → ℝ) (b b' : ℝ) :
    svmObjective X y 1 ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w') ((1 / 2) * b + (1 / 2) * b') ≤
      (1 / 2 : ℝ) * svmObjective X y 1 w b + (1 / 2 : ℝ) * svmObjective X y 1 w' b' := by
  have := (convexOn_svmObjective X y zero_le_one).2 (Set.mem_univ (w, b))
    (Set.mem_univ (w', b')) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simpa [smul_eq_mul] using this

example : (((Finset.univ : Finset (Fin 1)).filter fun k =>
      (![-1] : Fin 1 → ℝ) k * ((!![1] *ᵥ (![1] : Fin 1 → ℝ)) k + 0) ≤ 0).card : ℝ) ≤ 2 := by
  have h := card_misclassified_le_sum_hinge (m := 1) (ι := Fin 1) !![1] ![-1] ![1] 0
  have hs : ∑ k : Fin 1, max 0 (1 - (![-1] : Fin 1 → ℝ) k *
      ((!![1] *ᵥ (![1] : Fin 1 → ℝ)) k + 0)) = 2 := by
    simp [mulVec, dotProduct]
    norm_num
  linarith

end Cslib.MachineLearning.LogisticSVM
