/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.LatentVariable.ProbabilisticPCAMLE

open Cslib.MachineLearning.LatentVariable.ProbabilisticPCA MetaMathlibExt Matrix WithLp

-- The PPCA covariance of a `2 × 1` loading `(1, 0)ᵀ` with `σ² = 1/2`.
example : ppcaCov (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) (1 / 2) = !![3 / 2, 0; 0, 1 / 2] := by
  unfold ppcaCov
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [vecMul, dotProduct]

-- The sample mean of `0` and `2` on the line is `1`.
example : sampleMean (![toLp 2 ![0], toLp 2 ![2]] : Fin 2 → EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
  simp [weightedMean, Fin.sum_univ_two]

-- Exact recovery when the sample covariance has the PPCA form (no general-position premise).
example {xs : Fin 7 → EuclideanSpace ℝ (Fin 3)} {W₀ : Matrix (Fin 3) (Fin 1) ℝ} {σ₀2 : ℝ}
    (hσ₀ : 0 < σ₀2) (h : sampleCov xs = ppcaCov W₀ σ₀2) :
    IsMLE xs (sampleMean xs) W₀ σ₀2 :=
  isMLE_of_sampleCov_eq hσ₀ h

-- Rank-deficient data in the plane, `(0, 0)` and `(1, 0)`: the sample covariance is
-- `diag (1/4, 0)`, with trace `1/4`.
example : (sampleCov (![toLp 2 ![0, 0], toLp 2 ![1, 0]] :
    Fin 2 → EuclideanSpace ℝ (Fin 2))).trace = 1 / 4 := by
  simp [weightedScatter, weightedMean, Fin.sum_univ_two, trace, vecMulVec]
  norm_num

-- With no latent factors the noise-variance MLE is `tr S / d`, here `1/8`.
example (μ : EuclideanSpace ℝ (Fin 2)) {σ2 : ℝ} (hσ : 0 < σ2) :
    logLik (![toLp 2 ![0, 0], toLp 2 ![1, 0]] : Fin 2 → EuclideanSpace ℝ (Fin 2)) μ
        (0 : Matrix (Fin 2) (Fin 1) ℝ) σ2 ≤
      logLik (![toLp 2 ![0, 0], toLp 2 ![1, 0]] : Fin 2 → EuclideanSpace ℝ (Fin 2))
        (sampleMean (![toLp 2 ![0, 0], toLp 2 ![1, 0]] : Fin 2 → EuclideanSpace ℝ (Fin 2)))
        (0 : Matrix (Fin 2) (Fin 1) ℝ)
        ((sampleCov (![toLp 2 ![0, 0], toLp 2 ![1, 0]] :
          Fin 2 → EuclideanSpace ℝ (Fin 2))).trace / 2) := by
  have hT : (sampleCov (![toLp 2 ![0, 0], toLp 2 ![1, 0]] :
      Fin 2 → EuclideanSpace ℝ (Fin 2))).trace = 1 / 4 := by
    simp [weightedScatter, weightedMean, Fin.sum_univ_two, trace, vecMulVec]
    norm_num
  simpa using logLik_zero_le (q := 1) (by rw [hT]; norm_num) μ hσ

#print axioms logLik_zero_le
