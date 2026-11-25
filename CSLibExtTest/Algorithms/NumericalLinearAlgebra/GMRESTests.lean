/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.NumericalLinearAlgebra.GMRES

@[expose] public section

open Matrix Polynomial Cslib.Algorithms.NumericalLinearAlgebra.GMRES
open Cslib.MachineLearning.LeastSquares MathlibExt.LinearAlgebra.Matrix.ConjugateGradient

namespace CSLibExtTest.Algorithms.NumericalLinearAlgebra.GMRES

/-- GMRES iterates exist at every step. -/
example (A : Matrix (Fin 3) (Fin 3) ℝ) (b x₀ : Fin 3 → ℝ) : ∃ x, IsGMRESIterate A b x₀ 2 x :=
  exists_isGMRESIterate A b x₀ 2

/-- Step `0`: the only point of `x₀ + 𝒦_0 = {x₀}` is `x₀` itself. -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (b x₀ : Fin 2 → ℝ) : IsGMRESIterate A b x₀ 0 x₀ := by
  refine ⟨by simp [krylov], fun y hy => ?_⟩
  have : y - x₀ = 0 := by simpa [krylov] using hy
  rw [sub_eq_zero.1 this]

/-- For `A = I` one step suffices: any first GMRES iterate solves the system (the polynomial
`p(z) = 1 - z` kills `I`). -/
example (b x₀ x : Fin 2 → ℝ) (hx : IsGMRESIterate (1 : Matrix (Fin 2) (Fin 2) ℝ) b x₀ 1 x) :
    x = b := by
  have h := rss_le_of_isGMRESIterate hx (1 - X) (by
    rw [show (1 : ℝ[X]) - X = -(X - Polynomial.C 1) by simp]
    rw [natDegree_neg, natDegree_X_sub_C]) (by simp)
  have hp : aeval (1 : Matrix (Fin 2) (Fin 2) ℝ) ((1 : ℝ[X]) - X) = 0 := by simp
  rw [hp, zero_mulVec, dotProduct_zero] at h
  have h0 : rss 1 b x = 0 :=
    le_antisymm h (by unfold rss; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have := dotProduct_self_eq_zero.1 h0
  rw [one_mulVec, sub_eq_zero] at this
  exact this.symm

/-- Finite termination for an invertible `2 × 2` matrix: the second iterate is exact. -/
example (b x₀ x : Fin 2 → ℝ) (hx : IsGMRESIterate !![2, 1; 0, 3] b x₀ 2 x) :
    !![(2 : ℝ), 1; 0, 3] *ᵥ x = b :=
  mulVec_eq_of_isGMRESIterate_dim (by simp [det_fin_two]) hx

end CSLibExtTest.Algorithms.NumericalLinearAlgebra.GMRES
