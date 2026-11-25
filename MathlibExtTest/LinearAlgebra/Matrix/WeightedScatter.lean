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

-- Weighted Gram matrices: with `B = 1` and positive weights, `B * diagonal w * Bᵀ` is positive
-- definite.
example {k : Type*} [Fintype k] [DecidableEq k] {w : k → ℝ} (hw : ∀ e, 0 < w e) :
    ((1 : Matrix k k ℝ) * diagonal w * (1 : Matrix k k ℝ)ᵀ).PosDef := by
  refine (posDef_mul_diagonal_mul_transpose_iff fun e => (hw e).le).2 fun v hv => ?_
  obtain ⟨e, he⟩ := Function.ne_iff.1 hv
  exact ⟨e, hw e, by simpa using he⟩

-- A zero weight on the only column of a `1 × 1` matrix: the weighted Gram matrix is not positive
-- definite (it is still positive semidefinite).
example : ¬ ((1 : Matrix (Fin 1) (Fin 1) ℝ) * diagonal (fun _ => (0 : ℝ)) *
    (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).PosDef := by
  rw [posDef_mul_diagonal_mul_transpose_iff fun _ => le_rfl]
  intro h
  obtain ⟨e, he, -⟩ := h (fun _ => 1) (by simp [funext_iff])
  exact lt_irrefl _ he

#print axioms posDef_mul_diagonal_mul_transpose_iff

-- Quadratic diversity from pairwise dissimilarities, for any square `Q` and weights summing to one.
example (Q : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, w i * Q i i - w ⬝ᵥ Q *ᵥ w =
      w ⬝ᵥ (Matrix.of fun i j => Q i i + Q j j - 2 * Q i j) *ᵥ w / 2 :=
  (sum_mul_diag_sub_dotProduct_mulVec_eq hw Q).2

-- The corrected source form keeps the weighted diagonal correction.
example (δ : Matrix (Fin 3) (Fin 3) ℝ) (v w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, w i * (Matrix.of fun i j => v i + v j - δ i j / 2) i i -
        w ⬝ᵥ (Matrix.of fun i j => v i + v j - δ i j / 2) *ᵥ w =
      w ⬝ᵥ δ *ᵥ w / 2 - (∑ i, w i * δ i i) / 2 :=
  (sum_mul_diag_sub_dotProduct_mulVec_eq hw _).1 δ v fun _ _ => rfl

-- A concrete check with signed weights `(2, -1)`, a nonsymmetric `δ` with nonzero diagonal and
-- `v = (1, 3)`: both sides equal `-2`.
example :
    ∑ i, ![2, -1] i * (Matrix.of fun i j => ![1, 3] i + ![1, 3] j - !![1, 2; 4, 3] i j / 2) i i -
        ![2, -1] ⬝ᵥ (Matrix.of fun i j => ![1, 3] i + ![1, 3] j - !![1, 2; 4, 3] i j / 2) *ᵥ
          ![2, -1] = (-2 : ℝ) ∧
      ![2, -1] ⬝ᵥ !![1, 2; 4, 3] *ᵥ ![2, -1] / 2 - (∑ i, ![2, -1] i * !![1, 2; 4, 3] i i) / 2 =
        (-2 : ℝ) := by
  constructor <;> simp [Fin.sum_univ_two, dotProduct, mulVec] <;> norm_num

#print axioms sum_mul_diag_sub_dotProduct_mulVec_eq
