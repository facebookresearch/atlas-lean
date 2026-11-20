/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import CSLibExt.MachineLearning.NeuralTangentKernel

/-!
# Tests for the empirical neural tangent kernel
-/

@[expose] public section

open scoped Matrix

namespace CSLibExtTest.MachineLearning.NeuralTangentKernel

open Cslib.MachineLearning.NeuralTangentKernel

/-- Linear model: the NTK is constant and equals the linear kernel. -/
theorem test_linear_const (X : Matrix (Fin 2) (Fin 2) ℝ)
    (hX : X = !![1, 2; 0, 1])
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : F = fun θ : EuclideanSpace ℝ (Fin 2) => WithLp.toLp 2 (X *ᵥ ⇑θ)) :
    ntk 2 2 F (WithLp.toLp 2 ![0, 0])
        = ntk 2 2 F (WithLp.toLp 2 ![1, -1])
      ∧ ntk 2 2 F (WithLp.toLp 2 ![0, 0]) = !![5, 2; 2, 1] := by
  have h1 := ntk_linear 2 2 X F hF (WithLp.toLp 2 ![0, 0])
  have h2 := ntk_linear 2 2 X F hF (WithLp.toLp 2 ![1, -1])
  refine ⟨?_, ?_⟩
  · rw [h1, h2]
  · rw [h1, hX]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- Zero residual: the kernel-applied residual vanishes; reading this as
zero output velocity needs the gradient-flow hypothesis. -/
theorem test_zero_residual_zero_velocity (P n : ℕ)
    (F : EuclideanSpace ℝ (Fin P) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (θ : ℝ → EuclideanSpace ℝ (Fin P))
    (t : ℝ) (h : F (θ t) = y) :
    WithLp.toLp 2 ((ntk P n F (θ t)) *ᵥ ⇑(F (θ t) - y)) = 0 := by
  have h0 : ⇑(0 : EuclideanSpace ℝ (Fin n)) = (0 : Fin n → ℝ) := rfl
  have h1 : WithLp.toLp 2 (0 : Fin n → ℝ) = (0 : EuclideanSpace ℝ (Fin n)) := rfl
  rw [h, sub_self, h0, Matrix.mulVec_zero, h1]

/-- Scalar identity model: the NTK is the `1 × 1` identity. -/
theorem test_scalar_ntk (θ : EuclideanSpace ℝ (Fin 1)) :
    ntk 1 1 (fun θ' => θ') θ = 1 := by
  have hF : (fun θ' => θ')
      = fun θ'' : EuclideanSpace ℝ (Fin 1) =>
        WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ⇑θ'') := by
    funext θ''
    simp [Matrix.one_mulVec]
  have h := ntk_linear 1 1 1 (fun θ' => θ') hF θ
  rw [h, Matrix.transpose_one, Matrix.mul_one]

/-- Scalar identity model: evaluates the NTK-applied residual expression
(no derivative occurs in the statement). -/
theorem test_scalar_flow (y : EuclideanSpace ℝ (Fin 1))
    (θ : ℝ → EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    (-(WithLp.toLp 2 ((ntk 1 1 (fun θ' => θ') (θ t)) *ᵥ ⇑(θ t - y)))) 0
      = -((θ t) 0 - y 0) := by
  rw [test_scalar_ntk, Matrix.one_mulVec]
  simp [PiLp.sub_apply]

#print axioms grad_sqLoss
#print axioms gradient_flow_identity
#print axioms one_step_gd_remainder
#print axioms ntk_linear

end CSLibExtTest.MachineLearning.NeuralTangentKernel
