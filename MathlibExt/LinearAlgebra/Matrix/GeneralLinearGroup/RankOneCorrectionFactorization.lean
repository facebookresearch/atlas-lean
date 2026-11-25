/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.RankOneEmbedding

/-!
# Rank-one block diagonal factorization

Factorization of the full block-diagonal embedding as a `diag` embedding
times the rank-one correction.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix

/-- Block diagonal factors as `diag` embedding times rank-one correction. -/
theorem blockDiagonal_factor_rankOneCorrection (n : ℕ) (R : Type*) [Ring R]
    (s : GL (Fin (n + 1)) R) (p : GL (Fin 1) R) :
    BlockElementary.blockDiagonal s p =
      blockDiagonalOne (Fin (n + 1)) (Fin 1) R
          (s * rankOneEmbedding n R p) * rankOneCorrection n R p := by
  apply Units.ext
  simp only [BlockElementary.blockDiagonal_eq_blockDiagonalHom, coe_blockDiagonalHom,
    coe_blockDiagonalOne,
    rankOneCorrection, Units.val_mul]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, add_zero,
    zero_add]
  have h_inv :
      (↑(rankOneEmbedding n R p) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (↑(rankOneEmbedding n R p)⁻¹ :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 := by
    calc (↑(rankOneEmbedding n R p) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (↑(rankOneEmbedding n R p)⁻¹ :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R)
        = (↑(rankOneEmbedding n R p * (rankOneEmbedding n R p)⁻¹) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
          rw [Units.val_mul]
        _ = (↑(1 : GL (Fin (n + 1)) R) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
          rw [mul_inv_cancel]
        _ = 1 := rfl
  simp only [Matrix.mul_assoc, h_inv, Matrix.mul_one]

end Matrix.GeneralLinearGroup
