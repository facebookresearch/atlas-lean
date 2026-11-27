/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.LinearizedStability
public import MathlibExt.Analysis.Control.PolePlacement

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Stabilisation of controllable linear systems by linear feedback

A real linear control system `ẋ = A x + B u` satisfying the Kalman rank condition can be made
exponentially stable by a linear state feedback `u = K x` (Coron, *Control and Nonlinearity*,
AMS 2007, Corollary 10.12): by the pole-shifting theorem `A + B K` can be given the characteristic
polynomial `(X + 1)ⁿ`, so all its eigenvalues equal `-1`.
-/

open Polynomial Matrix

@[expose] public section

namespace MathlibExt.Analysis.Control

variable {n m : ℕ}

/-- **Controllable linear systems have a Hurwitz closed loop** (Coron, *Control and
Nonlinearity*, AMS 2007, Corollary 10.12). If `A ∈ ℝ^{n×n}` and `B ∈ ℝ^{n×m}` satisfy the Kalman
rank condition `Span {A^i B u : u ∈ ℝ^m, 0 ≤ i < n} = ℝⁿ`, there is `K ∈ ℝ^{m×n}` such that every
complex eigenvalue of `A + B K` has negative real part; in fact `K` can be chosen so that
`A + B K` has characteristic polynomial `(X + 1)ⁿ`. -/
theorem exists_isHurwitz_add_mul (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (hK : Submodule.span ℝ {x | ∃ i < n, ∃ u : Fin m → ℝ, x = (A ^ i * B) *ᵥ u} = ⊤) :
    ∃ K : Matrix (Fin m) (Fin n) ℝ, (A + B * K).charpoly = (X + 1) ^ n ∧
      (A + B * K).IsHurwitz := by
  have hK' : Submodule.span ℝ {x | ∃ i < Module.finrank ℝ (Fin n → ℝ), ∃ u : Fin m → ℝ,
      x = (toLin' A ^ i) (toLin' B u)} = ⊤ := by
    have hp : ∀ i : ℕ, toLin' A ^ i = toLin' (A ^ i) := by
      intro i
      induction i with
      | zero => simp; rfl
      | succ i ih => rw [pow_succ, ih, pow_succ, Matrix.toLin'_mul, Module.End.mul_eq_comp]
    rw [← hK, Module.finrank_fin_fun]
    congr 1
    ext x
    refine exists_congr fun i => and_congr_right fun _ => exists_congr fun u => ?_
    rw [hp, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec]
  obtain ⟨K', hK'⟩ := exists_charpoly_add_comp_eq (toLin' A) (toLin' B) hK' ((X + 1) ^ n)
    ((monic_X_add_C 1).pow n) (by rw [Module.finrank_fin_fun]; simp [natDegree_pow])
  set K := LinearMap.toMatrix' K'
  have hchar : (A + B * K).charpoly = (X + 1) ^ n := by
    have hlin : toLin' (A + B * K) = toLin' A + toLin' B ∘ₗ K' := by
      rw [map_add, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    rw [← hK', ← hlin, ← LinearMap.charpoly_toMatrix (toLin' (A + B * K)) (Pi.basisFun ℝ (Fin n)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  refine ⟨K, hchar, fun μ hμ => ?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map, hchar] at hμ
  simp only [IsRoot, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_one, eval_pow, eval_add, eval_X, eval_one] at hμ
  have : μ = -1 := by
    have := (pow_eq_zero_iff'.1 hμ).1
    linear_combination this
  rw [this]
  norm_num

/-- **Exponential stabilisation of controllable linear systems** (Coron, *Control and
Nonlinearity*, AMS 2007, Corollary 10.12). If `A ∈ ℝ^{n×n}` and `B ∈ ℝ^{n×m}` satisfy the Kalman
rank condition, there are a feedback matrix `K ∈ ℝ^{m×n}` and constants `M, α > 0` such that every
solution `x(t) = e^{t (A + B K)} x(0)` of the closed-loop system `ẋ = (A + B K) x` satisfies
`‖x(t)‖ ≤ M e^{-α t} ‖x(0)‖` for `t ≥ 0`; in particular `0` is globally asymptotically stable for
the closed loop. -/
theorem exists_norm_exp_add_mul_le (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (hK : Submodule.span ℝ {x | ∃ i < n, ∃ u : Fin m → ℝ, x = (A ^ i * B) *ᵥ u} = ⊤) :
    ∃ K : Matrix (Fin m) (Fin n) ℝ, ∃ M α : ℝ, 0 < M ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
      ∀ v : Fin n → ℝ, ‖NormedSpace.exp (t • (A + B * K)) *ᵥ v‖ ≤
        M * Real.exp (-(α * t)) * ‖v‖ := by
  obtain ⟨K, -, hH⟩ := exists_isHurwitz_add_mul A B hK
  exact ⟨K, hH.exists_norm_exp_smul_mulVec_le⟩

end MathlibExt.Analysis.Control
