/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.LQR.FiniteHorizon
import Mathlib.Tactic.NormNum

open Matrix ControlTheory

-- The dynamic-programming reading of `complete_square`: with
-- `K = (R + BᵀPB)⁻¹ BᵀPA`, the input `u⋆ = -Kx` attains the stage-cost
-- minimum `xᵀP'x`, and no input does better.
example {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {P Q : Matrix n n ℝ}
    {R : Matrix m m ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosDef) (x : n → ℝ) :
    (x ⬝ᵥ Q *ᵥ x
        + (-(((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)) ⬝ᵥ R *ᵥ
            (-(((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x))
        + (A *ᵥ x + B *ᵥ (-(((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)))
          ⬝ᵥ P *ᵥ (A *ᵥ x + B *ᵥ (-(((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)))
      = x ⬝ᵥ (riccatiStep A B P Q R) *ᵥ x)
    ∧ ∀ u : m → ℝ, x ⬝ᵥ (riccatiStep A B P Q R) *ᵥ x ≤
        x ⬝ᵥ Q *ᵥ x + u ⬝ᵥ R *ᵥ u + (A *ᵥ x + B *ᵥ u) ⬝ᵥ P *ᵥ (A *ᵥ x + B *ᵥ u) := by
  constructor
  · rw [complete_square hP hQ hR x (-(((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x))]
    simp
  · intro u
    rw [complete_square hP hQ hR x u]
    have hS : (0 : ℝ) ≤ (u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)
        ⬝ᵥ (R + Bᵀ * P * B) *ᵥ (u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x) := by
      have h := (posDef_R_add_transpose_mul_mul (B := B) hP hR).posSemidef
        |>.dotProduct_mulVec_nonneg (u + ((R + Bᵀ * P * B)⁻¹ * Bᵀ * P * A) *ᵥ x)
      simpa [star_trivial] using h
    linarith

-- Boundary `P = 0`: the step returns the stage state cost unchanged.
example {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) :
    riccatiStep A B 0 Q R = Q := by
  simp [riccatiStep]

-- Boundary `B = 0`: no control authority, the step is `Q + AᵀPA`.
example {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix n n ℝ) (P Q : Matrix n n ℝ) (R : Matrix m m ℝ) :
    riccatiStep A 0 P Q R = Q + Aᵀ * P * A := by
  simp [riccatiStep]

-- Scalar closed form (`n = m = 1`, via `Fin 1` diagonals): with
-- `A = 2, B = 1, P = 3, Q = 5, R = 7`, the step is `5 + 12 - 36/10`.
example :
    riccatiStep (Matrix.diagonal (fun _ : Fin 1 => (2 : ℝ)))
        (Matrix.diagonal (fun _ : Fin 1 => (1 : ℝ)))
        (Matrix.diagonal (fun _ : Fin 1 => (3 : ℝ)))
        (Matrix.diagonal (fun _ : Fin 1 => (5 : ℝ)))
        (Matrix.diagonal (fun _ : Fin 1 => (7 : ℝ))) 0 0 = 67 / 5 := by
  simp [riccatiStep, Matrix.mul_apply, Fin.sum_univ_one]
  norm_num

#print axioms posDef_R_add_transpose_mul_mul
#print axioms complete_square
#print axioms riccatiStep_posSemidef
