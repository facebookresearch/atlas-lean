/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.GaussianMLE

open MetaMathlibExt Matrix WithLp Real

-- The log-density at the mean with identity covariance is `-(n / 2) log (2 π)`.
example (μ : EuclideanSpace ℝ (Fin 3)) :
    log (multivariateGaussianPDFReal μ 1 μ) = -(3 / 2) * log (2 * π) := by
  rw [log_multivariateGaussianPDFReal μ PosDef.one]
  simp

-- The classical Gaussian MLE (all weights one): the sample mean and the sample covariance
-- maximize the log-likelihood over all means and positive definite covariances.
example (xs : Fin 6 → EuclideanSpace ℝ (Fin 2))
    (hspan : ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → ∃ i j, inner ℝ v (xs i) ≠ inner ℝ v (xs j))
    (μ : EuclideanSpace ℝ (Fin 2)) {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosDef) :
    ∑ i, log (multivariateGaussianPDFReal μ S (xs i)) ≤
      ∑ i, log (multivariateGaussianPDFReal (weightedMean 1 xs)
        (weightedScatter 1 xs (weightedMean 1 xs)) (xs i)) := by
  simpa using sum_mul_log_multivariateGaussianPDFReal_le (w := 1) (fun _ => one_pos) hspan μ hS

-- The MLE under a positive definite weighted sample covariance, without general position.
example (w : Fin 4 → ℝ) (hW : 0 < ∑ i, w i) (xs : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (hC : (weightedScatter w xs (weightedMean w xs)).PosDef) (μ : EuclideanSpace ℝ (Fin 2))
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosDef) :
    ∑ i, w i * log (multivariateGaussianPDFReal μ S (xs i)) ≤
      ∑ i, w i * log (multivariateGaussianPDFReal (weightedMean w xs)
        (weightedScatter w xs (weightedMean w xs)) (xs i)) :=
  sum_mul_log_multivariateGaussianPDFReal_le_of_posDef hW hC μ hS

#print axioms sum_mul_log_multivariateGaussianPDFReal_le
