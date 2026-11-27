/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction

/-- Channel eigenvalues are nonnegative for the identity noise
covariance. -/
example (H : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    0 ≤ channelEigenvalues H Matrix.PosDef.one i :=
  channelEigenvalues_nonneg H Matrix.PosDef.one i

/-- Rank-deficient channel `diag(1, 0)`, `R = 1`, off-diagonal `K = [[1, 1/2], [1/2, 1]]`:
`det (1 + H K Hᵀ) = 2`, which equals `∏ (1 + λ_i K_ii) = (1 + 1)(1 + 0)` in the basis `V = 1`. -/
example :
    detRatio !![(1 : ℝ), 0; 0, 0] 1 !![(1 : ℝ), 1 / 2; 1 / 2, 1] = 2 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [detRatio, Matrix.det_fin_two, Matrix.det_one, div_one, Matrix.add_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne h01, Matrix.one_apply_ne h10, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons]
  norm_num

/-- Channel `diag(1, 2)`, `R = 1` (`λ = (1, 4)`, basis `V = 1`), off-diagonal
`K = [[1, 1/2], [1/2, 1]]`: `det (1 + H K Hᵀ) = 9 < 10 = (1 + 1)(1 + 4)`, so dropping the
off-diagonal correlation strictly helps. -/
example :
    detRatio !![(1 : ℝ), 0; 0, 2] 1 !![(1 : ℝ), 1 / 2; 1 / 2, 1] <
      ∏ i, (1 + ![(1 : ℝ), 4] i * (!![(1 : ℝ), 1 / 2; 1 / 2, 1]) i i) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [detRatio, Matrix.det_fin_two, Matrix.det_one, div_one, Fin.prod_univ_two,
    Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne h01, Matrix.one_apply_ne h10, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons]
  norm_num

/-- Violated premise: the symmetric but indefinite
`K = [[-2, 1, 0], [1, -2, 0], [0, 0, -2]]` with `H = R = 1` (`λ = 1`, `V = 1`) has
`det (1 + K) = 0 > -1 = ∏ (1 + K_ii)`, so the PSD hypothesis cannot be dropped. -/
example :
    ∏ i, (1 + (1 : ℝ) * (!![(-2 : ℝ), 1, 0; 1, -2, 0; 0, 0, -2]) i i) <
      detRatio (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 !![(-2 : ℝ), 1, 0; 1, -2, 0; 0, 0, -2] := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [detRatio, Matrix.det_fin_three, Matrix.det_one, div_one, Fin.prod_univ_three,
    Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne h01, Matrix.one_apply_ne h02,
    Matrix.one_apply_ne h10, Matrix.one_apply_ne h12, Matrix.one_apply_ne h20,
    Matrix.one_apply_ne h21, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  norm_num


/-- The diagonalized covariance is positive semidefinite and its
trace (total power) is preserved for the identity channel. -/
example (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosSemidef) :
    (diagonalizedCovariance (1 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.PosDef.one K).PosSemidef ∧
      (diagonalizedCovariance (1 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.PosDef.one K).trace =
        K.trace :=
  ⟨diagonalizedCovariance_posSemidef (1 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.PosDef.one hK,
    trace_diagonalizedCovariance (1 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.PosDef.one K⟩

/-- Diagonalization cannot decrease the determinant ratio. -/
example (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosSemidef) :
    detRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 K ≤
      detRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 (diagonalizedCovariance (1 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.PosDef.one K) :=
  detRatio_le_detRatio_diagonalizedCovariance (1 : Matrix (Fin 2) (Fin 2) ℝ) Matrix.PosDef.one hK

end MathlibExtTest.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction
