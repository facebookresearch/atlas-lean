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
# Weak block LDU identity

For `B : (Fin n) × (Fin 1)`, `C : (Fin 1) × (Fin n)`,
`T, S : GL (Fin n)`, `t : GL (Fin 1)`:

`upperUnit B * blockDiagonal T t * lowerUnit C * blockDiagonalOne S = 1`

implies `B = 0`, `C = 0`, `t = 1`, `T * S = 1`
by expanding `fromBlocks` and cancelling invertible `t` and `S`.
Separate `T = 1` and `S = 1` is not claimed. Proof uniform for `n = 0`.
Uses weakest robust `Ring` API; if `Field` needed we would note it.
-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup
namespace BlockElementary

open Matrix

variable {n : ℕ} {R : Type*} [Ring R]

/-- Weak uniqueness: upper * diag * lower * diagOne = 1 gives
`B = 0`, `C = 0`, `t = 1`, `T * S = 1`. Not `T = 1`, `S = 1`. -/
theorem weakBlockLDU_eq_one
    {B : Matrix (Fin n) (Fin 1) R} {C : Matrix (Fin 1) (Fin n) R}
    {T S : GL (Fin n) R} {t : GL (Fin 1) R}
    (h : upperUnit (α := Fin n) (β := Fin 1) B *
      blockDiagonal (α := Fin n) (β := Fin 1) T t *
      lowerUnit (α := Fin n) (β := Fin 1) C *
      blockDiagonalOne (Fin n) (Fin 1) R S = 1) :
    B = 0 ∧ C = 0 ∧ t = 1 ∧ T * S = 1 := by
  have hM0 := congrArg Units.val h
  simp only [Units.val_mul, Units.val_one] at hM0
  rw [coe_upperUnit, blockDiagonal_eq_blockDiagonalHom, coe_blockDiagonalHom,
    coe_lowerUnit, coe_blockDiagonalOne] at hM0
  have hF : fromBlocks (((↑T : Matrix (Fin n) (Fin n) R) +
      B * (↑t : Matrix (Fin 1) (Fin 1) R) * C) *
      (↑S : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R)
      (B * (↑t : Matrix (Fin 1) (Fin 1) R))
      (((↑t : Matrix (Fin 1) (Fin 1) R) * C) * (↑S : Matrix (Fin n) (Fin n) R))
      (↑t : Matrix (Fin 1) (Fin 1) R) = 1 := by
    simpa only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.mul_assoc,
      Matrix.add_mul, Matrix.mul_add] using hM0
  rw [← fromBlocks_one] at hF
  have hBt : B * (↑t : Matrix (Fin 1) (Fin 1) R) = 0 := by
    ext i j
    simpa [fromBlocks_apply₁₂] using congrFun (congrFun hF (Sum.inl i)) (Sum.inr j)
  have htC : ((↑t : Matrix (Fin 1) (Fin 1) R) * C) *
      (↑S : Matrix (Fin n) (Fin n) R) = 0 := by
    ext i j
    simpa [fromBlocks_apply₂₁] using congrFun (congrFun hF (Sum.inr i)) (Sum.inl j)
  have ht1 : (↑t : Matrix (Fin 1) (Fin 1) R) = 1 := by
    ext i j
    simpa [fromBlocks_apply₂₂] using congrFun (congrFun hF (Sum.inr i)) (Sum.inr j)
  have hTS : ((↑T : Matrix (Fin n) (Fin n) R) +
      B * (↑t : Matrix (Fin 1) (Fin 1) R) * C) *
      (↑S : Matrix (Fin n) (Fin n) R) = 1 := by
    ext i j
    simpa [fromBlocks_apply₁₁] using congrFun (congrFun hF (Sum.inl i)) (Sum.inl j)
  have hB : B = 0 := by
    calc B = B * (1 : Matrix (Fin 1) (Fin 1) R) := by rw [Matrix.mul_one]
      _ = B * (↑t : Matrix (Fin 1) (Fin 1) R) := by rw [ht1]
      _ = 0 := hBt
  have hCS : C * (↑S : Matrix (Fin n) (Fin n) R) = 0 := by
    calc C * (↑S : Matrix (Fin n) (Fin n) R)
        = (↑t : Matrix (Fin 1) (Fin 1) R) * C *
          (↑S : Matrix (Fin n) (Fin n) R) := by
          rw [ht1, Matrix.one_mul]
      _ = 0 := htC
  have hC : C = 0 := by
    calc C = C * (1 : Matrix (Fin n) (Fin n) R) := by rw [Matrix.mul_one]
      _ = C * (↑S * S.inv : Matrix (Fin n) (Fin n) R) := by rw [← S.val_inv]
      _ = C * (↑S : Matrix (Fin n) (Fin n) R) * S.inv := by
        rw [Matrix.mul_assoc]
      _ = (0 : Matrix (Fin 1) (Fin n) R) * S.inv := by rw [hCS]
      _ = 0 := by rw [Matrix.zero_mul]
  have ht : t = 1 := Units.ext ht1
  have hTSl : T * S = 1 := by
    apply Units.ext
    calc (↑(T * S) : Matrix (Fin n) (Fin n) R)
        = (↑T : Matrix (Fin n) (Fin n) R) *
          (↑S : Matrix (Fin n) (Fin n) R) := rfl
      _ = ((↑T : Matrix (Fin n) (Fin n) R) +
          B * (↑t : Matrix (Fin 1) (Fin 1) R) * C) *
          (↑S : Matrix (Fin n) (Fin n) R) := by rw [hB, hC]; simp
      _ = 1 := hTS
  exact ⟨hB, hC, ht, hTSl⟩

end BlockElementary
end GeneralLinearGroup
end Matrix
