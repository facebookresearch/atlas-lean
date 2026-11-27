/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Matrix.BauerFikeDiagonalizable
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Analysis.Matrix.BauerFikeDiagonalizable
open scoped Matrix.Norms.L2Operator

namespace MathlibExtTest.Analysis.Matrix.BauerFikeDiagonalizable

/-- The hypotheses are satisfiable: for the `1 × 1` matrices `A = diag(0)` (with `V = 1`) and
`E = I`, the eigenvalue `μ = 1` of `A + E` is within `‖I‖ ‖I‖ ‖E‖ = 1` of the eigenvalue `0`
of `A`, and the bound is attained. -/
example : ∃ i, ‖(1 : ℂ) - (fun _ : Fin 1 => (0 : ℂ)) i‖ ≤
    ‖((1 : (Matrix (Fin 1) (Fin 1) ℂ)ˣ) : Matrix (Fin 1) (Fin 1) ℂ)‖ *
      ‖(↑(1 : (Matrix (Fin 1) (Fin 1) ℂ)ˣ)⁻¹ : Matrix (Fin 1) (Fin 1) ℂ)‖ *
      ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖ := by
  refine exists_norm_sub_le_of_mem_spectrum_add 1 (fun _ => 0) 1 ?_
  rw [spectrum.mem_iff]
  simp

/-- The exclusion form in the Banach algebra `ℂ`: `μ = 3 ∈ σ(1 + 2)`, `3 - 1 = 2` invertible,
and `1 ≤ ‖2⁻¹‖ ‖2‖ = 1`. -/
example : 1 ≤ ‖Ring.inverse (algebraMap ℂ ℂ 3 - 1)‖ * ‖(2 : ℂ)‖ := by
  refine one_le_norm_inverse_mul_norm_of_mem_spectrum_add (A := (1 : ℂ)) ?_ ?_
  · rw [spectrum.mem_iff]; norm_num
  · norm_num

/-- The non-unitary eigenvector matrix `V = [[1, 1], [0, 1]]`, with inverse `[[1, -1], [0, 1]]`. -/
def V2 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A `2 × 2` instance with `κ(V) > 1`: `A = V diag(1, 2) V⁻¹ = [[1, 1], [0, 2]]` and `E = 0`;
the eigenvalue `μ = 1` of `A + E` satisfies the bound with `i = 0`. -/
example : ∃ i, ‖(1 : ℂ) - ![1, 2] i‖ ≤
    ‖((V2 : Matrix (Fin 2) (Fin 2) ℂ))‖ * ‖(↑V2⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)‖ *
      ‖(0 : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
  refine exists_norm_sub_le_of_mem_spectrum_add V2 ![1, 2] 0 ?_
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  have h : algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) 1 -
      ((V2 : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![1, 2] *
        (↑V2⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) + 0) = !![0, -1; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply] <;> norm_num
  rw [h, Matrix.det_fin_two_of]
  simp

end MathlibExtTest.Analysis.Matrix.BauerFikeDiagonalizable
