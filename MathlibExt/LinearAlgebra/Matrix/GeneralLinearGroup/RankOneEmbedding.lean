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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockElementary

/-!
# Rank-one diagonal correction basics

Rank-one embedding `GL (Fin 1) → GL (Fin (n+1))` via `diag(A, 1)` and reindexing,
and the diagonal correction in `GL (Fin (n+1) ⊕ Fin 1)`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix

/-- Rank-one embedding `GL (Fin 1) →* GL (Fin (n+1))` via `diag` and reindexing. -/
def rankOneEmbedding (n : ℕ) (R : Type*) [Semiring R] : GL (Fin 1) R →* GL (Fin (n + 1)) R :=
  (reindexMulEquiv (((Equiv.cast (congrArg Fin (Nat.add_comm n 1))).trans
    (finSumFinEquiv (m := 1) (n := n)).symm).symm)).toMonoidHom.comp
    (blockDiagonalOne (Fin 1) (Fin n) R)

@[simp]
theorem rankOneEmbedding_apply (n : ℕ) (R : Type*) [Semiring R] (p : GL (Fin 1) R) :
    rankOneEmbedding n R p =
      (reindexMulEquiv (((Equiv.cast (congrArg Fin (Nat.add_comm n 1))).trans
        (finSumFinEquiv (m := 1) (n := n)).symm).symm) (blockDiagonalOne (Fin 1) (Fin n) R p)) :=
  rfl

/-- Diagonal correction pairing `diag` embedding inverse with `p` in `GL (Fin (n+1) ⊕ Fin 1)`. -/
def rankOneCorrection (n : ℕ) (R : Type*) [Ring R] (p : GL (Fin 1) R) :
    GL (Fin (n + 1) ⊕ Fin 1) R :=
  BlockElementary.blockDiagonal (rankOneEmbedding n R p)⁻¹ p

@[simp]
theorem det_rankOneEmbedding {R : Type*} [CommRing R] (n : ℕ) (p : GL (Fin 1) R) :
    det (rankOneEmbedding n R p) = det p := by
  simp only [rankOneEmbedding_apply, det_reindexMulEquiv, det_blockDiagonalOne]

@[simp]
theorem det_rankOneCorrection {R : Type*} [CommRing R] (n : ℕ) (p : GL (Fin 1) R) :
    det (rankOneCorrection n R p) = 1 := by
  simp only [rankOneCorrection, BlockElementary.det_blockDiagonal, det_rankOneEmbedding,
    map_inv, inv_mul_cancel]

end Matrix.GeneralLinearGroup
