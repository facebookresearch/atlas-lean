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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockUnipotent

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Determinant
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization

/-!
# Block-diagonal matrices

Block-diagonal matrices in `GL (α ⊕ β)` via the embedding `GL α × GL β → GL (α ⊕ β)`,
with determinant multiplicativity and elementary-subgroup embeddings.
-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup
namespace BlockElementary

open Matrix

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
variable {R : Type*} [Ring R]

/-- Full block-diagonal embedding `GL α × GL β → GL (α ⊕ β)`. -/
def blockDiagonal (g : GL α R) (h : GL β R) : GL (α ⊕ β) R :=
  _root_.Matrix.GeneralLinearGroup.blockDiagonalHom α β R (g, h)

/-- The existing Ring API is the canonical bundled block homomorphism. -/
theorem blockDiagonal_eq_blockDiagonalHom (g : GL α R) (h : GL β R) :
    blockDiagonal g h =
      _root_.Matrix.GeneralLinearGroup.blockDiagonalHom α β R (g, h) :=
  rfl

@[simp]
lemma coe_blockDiagonal (g : GL α R) (h : GL β R) :
    (↑(blockDiagonal g h) : Matrix (α ⊕ β) (α ⊕ β) R) =
      fromBlocks (↑g : Matrix α α R) (0 : Matrix α β R) (0 : Matrix β α R)
        (↑h : Matrix β β R) := by
  rw [blockDiagonal_eq_blockDiagonalHom]
  exact _root_.Matrix.GeneralLinearGroup.coe_blockDiagonalHom g h

/-- The inverse retains the original two inverse blocks and zero cross terms. -/
theorem coe_blockDiagonal_inv (g : GL α R) (h : GL β R) :
    (↑((blockDiagonal g h)⁻¹) : Matrix (α ⊕ β) (α ⊕ β) R) =
      fromBlocks (↑(g⁻¹) : Matrix α α R) (0 : Matrix α β R) (0 : Matrix β α R)
        (↑(h⁻¹) : Matrix β β R) := by
  rw [blockDiagonal_eq_blockDiagonalHom, ← map_inv]
  exact _root_.Matrix.GeneralLinearGroup.coe_blockDiagonalHom (g⁻¹) (h⁻¹)

variable {S : Type*} [CommRing S]
variable {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] [Fintype γ] [Fintype δ]

@[simp]
theorem det_blockDiagonal (g : GL γ S) (h : GL δ S) :
    _root_.Matrix.GeneralLinearGroup.det (blockDiagonal g h) =
      _root_.Matrix.GeneralLinearGroup.det g *
        _root_.Matrix.GeneralLinearGroup.det h := by
  apply Units.ext
  rw [_root_.Matrix.GeneralLinearGroup.val_det_apply, coe_blockDiagonal,
    Matrix.det_fromBlocks_zero₂₁]
  rfl

theorem blockDiagonalOne_mem_elementarySubgroup
    {g : GL α R}
    (hg : g ∈ _root_.Matrix.GeneralLinearGroup.elementarySubgroup α R) :
    _root_.Matrix.GeneralLinearGroup.blockDiagonalOne α β R g ∈
      _root_.Matrix.GeneralLinearGroup.elementarySubgroup (α ⊕ β) R := by
  have hle :
      Subgroup.closure
          (_root_.Matrix.GeneralLinearGroup.elementarySet α R) ≤
        (_root_.Matrix.GeneralLinearGroup.elementarySubgroup (α ⊕ β) R).comap
          (_root_.Matrix.GeneralLinearGroup.blockDiagonalOne α β R) := by
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨i, j, hij, a, rfl⟩ := hy
    change _root_.Matrix.GeneralLinearGroup.blockDiagonalOne α β R
        (_root_.Matrix.GeneralLinearGroup.elementary i j hij a) ∈
        _root_.Matrix.GeneralLinearGroup.elementarySubgroup (α ⊕ β) R
    rw [_root_.Matrix.GeneralLinearGroup.blockDiagonalOne_elementary]
    exact _root_.Matrix.GeneralLinearGroup.elementary_mem_elementarySubgroup
      _ _ _ _
  exact (Subgroup.mem_comap).mp (hle hg)

end BlockElementary
end GeneralLinearGroup
end Matrix
