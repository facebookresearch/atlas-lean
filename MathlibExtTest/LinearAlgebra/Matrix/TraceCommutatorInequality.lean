/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.TraceCommutatorInequality

/-!
# Tests for `tr (XY)² ≤ tr X²Y²`
-/

open scoped ComplexOrder

namespace MathlibExtTest.LinearAlgebra.Matrix.TraceCommutatorInequality

open MathlibExt.LinearAlgebra.Matrix.TraceCommutatorInequality

/-- The Pauli matrix `σ_z`. -/
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrix `σ_x`. -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

lemma σz_herm : σz.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σz, Matrix.conjTranspose_apply]

lemma σx_herm : σx.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σx, Matrix.conjTranspose_apply]

/-- The inequality for two anticommuting Pauli matrices. -/
example : (σz * σx * σz * σx).trace ≤ (σz * σz * σx * σx).trace :=
  trace_mul_mul_mul_mul_le σz_herm σx_herm

/-- It is strict there: `tr (σ_z σ_x)² = -2` while `tr σ_z² σ_x² = 2`. -/
example : (σz * σx * σz * σx).trace = -2 ∧ (σz * σz * σx * σx).trace = 2 := by
  constructor <;>
  · simp [σz, σx, Matrix.trace, Fin.sum_univ_two]
    norm_num

/-- The case `t = 2` of the Lieb–Thirring trace inequality applies to any pair of
positive-semidefinite matrices, for instance `1` and `1`. -/
example : RCLike.re (cfc (· ^ ((2 : ℝ) * 1) : ℝ → ℝ)
      (cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 *
        cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace ≤
    RCLike.re (cfc (· ^ (1 : ℝ) : ℝ → ℝ)
      (cfc (· ^ ((2 : ℝ) / 2) : ℝ → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        cfc (· ^ (2 : ℝ) : ℝ → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        cfc (· ^ ((2 : ℝ) / 2) : ℝ → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ))).trace :=
  araki_lieb_thirring_two_one Matrix.PosSemidef.one Matrix.PosSemidef.one

end MathlibExtTest.LinearAlgebra.Matrix.TraceCommutatorInequality
