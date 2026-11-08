/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.WeightedScatter

open MetaMathlibExt Matrix WithLp

-- The weighted mean of `0` and `2` on the line with weights `1, 3` is `3 / 2`.
example : weightedMean ![1, 3] (![toLp 2 ![0], toLp 2 ![2]] : Fin 2 → EuclideanSpace ℝ (Fin 1)) 0
    = 3 / 2 := by
  simp [weightedMean, Fin.sum_univ_two]
  norm_num

-- Their weighted scatter about the mean is the weighted variance `3 / 4`.
example : weightedScatter ![1, 3] (![toLp 2 ![0], toLp 2 ![2]] : Fin 2 → EuclideanSpace ℝ (Fin 1))
    (toLp 2 ![3 / 2]) 0 0 = 3 / 4 := by
  simp [weightedScatter, Fin.sum_univ_two, vecMulVec]
  norm_num

-- The bias-variance split, for any symmetric `A`.
example (w : Fin 4 → ℝ) (hw : ∑ i, w i ≠ 0) (xs : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : Aᵀ = A) (μ : EuclideanSpace ℝ (Fin 2)) :
    ∑ i, w i * (ofLp (xs i - μ) ⬝ᵥ A *ᵥ ofLp (xs i - μ)) =
      ∑ i, w i * (ofLp (xs i - weightedMean w xs) ⬝ᵥ A *ᵥ ofLp (xs i - weightedMean w xs)) +
        (∑ i, w i) * (ofLp (weightedMean w xs - μ) ⬝ᵥ A *ᵥ ofLp (weightedMean w xs - μ)) :=
  sum_mul_quad_sub_eq hw xs hA μ

#print axioms weightedScatter_posDef
