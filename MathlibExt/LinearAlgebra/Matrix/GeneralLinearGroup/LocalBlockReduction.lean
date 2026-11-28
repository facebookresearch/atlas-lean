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
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.LocalPivot
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Schur complements and elementary reduction over local rings

For an invertible finite block matrix `g = [[A, B], [C, D]]` over a
commutative ring with `D` invertible, the Schur complement
`A - B * D⁻¹ * C` is invertible. Upper and lower block-elementary factors
clear `g` to the block diagonal matrix with that complement and `D`.

Over a commutative local ring, an invertible matrix indexed by a finite set
plus one distinguished coordinate can first be moved by elementary
operations so that its distinguished diagonal entry is a unit. It then
admits two-sided elementary reduction to an invertible block on the finite
set and an invertible one-dimensional block. Their determinants multiply
to the determinant of the original matrix.
-/

@[expose] public section

open Matrix
open Matrix.GeneralLinearGroup

namespace Matrix.GeneralLinearGroup

section Schur22

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
  [Fintype α] [Fintype β]
variable {R : Type*} [CommRing R]

/-- For an invertible block matrix over a commutative ring with finite
block index sets and an invertible lower-right block `D`, the Schur
complement `A - B * D⁻¹ * C` is invertible. -/
theorem isUnit_schurComplement₂₂
    (g : GL (α ⊕ β) R) [Invertible g.val.toBlocks₂₂] :
    IsUnit
      (g.val.toBlocks₁₁ -
        g.val.toBlocks₁₂ * ⅟(g.val.toBlocks₂₂) * g.val.toBlocks₂₁) := by
  have hU : IsUnit g.val := ⟨g, rfl⟩
  have h_eq :
      g.val =
        fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂
          g.val.toBlocks₂₁ g.val.toBlocks₂₂ :=
    (fromBlocks_toBlocks g.val).symm
  have h_isUnit_fromBlocks :
      IsUnit
        (fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂
          g.val.toBlocks₂₁ g.val.toBlocks₂₂) :=
    h_eq ▸ hU
  exact
    (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂).mp
      h_isUnit_fromBlocks

/-- Bundle the invertible Schur complement `A - B * D⁻¹ * C` of an
invertible finite block matrix over a commutative ring whose lower-right
block `D` is invertible. -/
noncomputable def schurComplement₂₂Unit
    (g : GL (α ⊕ β) R) [Invertible g.val.toBlocks₂₂] : GL α R :=
  (isUnit_schurComplement₂₂ g).unit

@[simp]
theorem coe_schurComplement₂₂Unit
    (g : GL (α ⊕ β) R) [Invertible g.val.toBlocks₂₂] :
    (schurComplement₂₂Unit (α := α) (β := β) g : Matrix α α R) =
      g.val.toBlocks₁₁ -
        g.val.toBlocks₁₂ * ⅟(g.val.toBlocks₂₂) * g.val.toBlocks₂₁ :=
  IsUnit.unit_spec (isUnit_schurComplement₂₂ g)

/-- For an invertible finite block matrix over a commutative ring with
invertible lower-right block `D`, multiply on the left by the upper block
factor with entry `-B * D⁻¹` and on the right by the lower block factor
with entry `-D⁻¹ * C`. The result is `diag(A - B * D⁻¹ * C, D)`. -/
theorem upper_mul_mul_lower_eq_blockDiagonal_schur
    (g : GL (α ⊕ β) R) [Invertible g.val.toBlocks₂₂] :
    BlockElementary.upperUnit (-(g.val.toBlocks₁₂ * ⅟(g.val.toBlocks₂₂))) *
        g *
      BlockElementary.lowerUnit
        (-(⅟(g.val.toBlocks₂₂) * g.val.toBlocks₂₁)) =
      BlockElementary.blockDiagonal
        (schurComplement₂₂Unit g) (unitOfInvertible g.val.toBlocks₂₂) := by
  let A := g.val.toBlocks₁₁
  let B := g.val.toBlocks₁₂
  let C := g.val.toBlocks₂₁
  let D := g.val.toBlocks₂₂
  have h_g_eq : g.val = fromBlocks A B C D :=
    (fromBlocks_toBlocks g.val).symm
  have h_s_eq :
      (schurComplement₂₂Unit (α := α) (β := β) g : Matrix α α R) =
        A - B * ⅟D * C :=
    coe_schurComplement₂₂Unit g
  have h_LDU :
      fromBlocks A B C D =
        fromBlocks (1 : Matrix α α R) (B * ⅟D)
            (0 : Matrix β α R) (1 : Matrix β β R) *
          fromBlocks (A - B * ⅟D * C) (0 : Matrix α β R)
            (0 : Matrix β α R) D *
          fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
            (⅟D * C) (1 : Matrix β β R) :=
    Matrix.fromBlocks_eq_of_invertible₂₂ A B C D
  have h_inv_upper :
      fromBlocks (1 : Matrix α α R) (-(B * ⅟D))
          (0 : Matrix β α R) (1 : Matrix β β R) *
        fromBlocks (1 : Matrix α α R) (B * ⅟D)
          (0 : Matrix β α R) (1 : Matrix β β R) =
        (1 : Matrix (α ⊕ β) (α ⊕ β) R) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have h_inv_lower :
      fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
          (⅟D * C) (1 : Matrix β β R) *
        fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
          (-(⅟D * C)) (1 : Matrix β β R) =
        (1 : Matrix (α ⊕ β) (α ⊕ β) R) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  apply Units.ext
  -- expand GL products to matrix products
  have h_mul_expand :
      (BlockElementary.upperUnit (-(B * ⅟D)) * g *
        BlockElementary.lowerUnit (-(⅟D * C))).val =
        (BlockElementary.upperUnit (-(B * ⅟D))).val *
          g.val *
          (BlockElementary.lowerUnit (-(⅟D * C))).val := by
    simp [Units.val_mul]
  rw [h_mul_expand]
  simp only [BlockElementary.coe_upperUnit, BlockElementary.coe_lowerUnit,
    BlockElementary.blockDiagonal_eq_blockDiagonalHom, coe_blockDiagonalHom, h_s_eq]
  -- isolate middle g.val
  calc
    fromBlocks (1 : Matrix α α R) (-(B * ⅟D))
          (0 : Matrix β α R) (1 : Matrix β β R) *
        g.val *
        fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
          (-(⅟D * C)) (1 : Matrix β β R)
      = fromBlocks (1 : Matrix α α R) (-(B * ⅟D))
            (0 : Matrix β α R) (1 : Matrix β β R) *
          fromBlocks A B C D *
          fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
            (-(⅟D * C)) (1 : Matrix β β R) := by
        rw [h_g_eq]
    _ = fromBlocks (1 : Matrix α α R) (-(B * ⅟D))
            (0 : Matrix β α R) (1 : Matrix β β R) *
          (fromBlocks (1 : Matrix α α R) (B * ⅟D)
              (0 : Matrix β α R) (1 : Matrix β β R) *
            fromBlocks (A - B * ⅟D * C) (0 : Matrix α β R)
              (0 : Matrix β α R) D *
            fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
              (⅟D * C) (1 : Matrix β β R)) *
          fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
            (-(⅟D * C)) (1 : Matrix β β R) := by
        rw [← h_LDU]
    _ = fromBlocks (A - B * ⅟D * C) (0 : Matrix α β R)
          (0 : Matrix β α R) D := by
        -- cancel left and right factors
        have h_left_cancel :
            fromBlocks (1 : Matrix α α R) (-(B * ⅟D))
                (0 : Matrix β α R) (1 : Matrix β β R) *
              fromBlocks (1 : Matrix α α R) (B * ⅟D)
                (0 : Matrix β α R) (1 : Matrix β β R) =
              (1 : Matrix (α ⊕ β) (α ⊕ β) R) := h_inv_upper
        have h_right_cancel :
            fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
                (⅟D * C) (1 : Matrix β β R) *
              fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
                (-(⅟D * C)) (1 : Matrix β β R) =
              (1 : Matrix (α ⊕ β) (α ⊕ β) R) := h_inv_lower
        calc
          fromBlocks (1 : Matrix α α R) (-(B * ⅟D))
                (0 : Matrix β α R) (1 : Matrix β β R) *
              (fromBlocks (1 : Matrix α α R) (B * ⅟D)
                  (0 : Matrix β α R) (1 : Matrix β β R) *
                fromBlocks (A - B * ⅟D * C) (0 : Matrix α β R)
                  (0 : Matrix β α R) D *
                fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
                  (⅟D * C) (1 : Matrix β β R)) *
              fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
                (-(⅟D * C)) (1 : Matrix β β R)
            = (fromBlocks (1 : Matrix α α R) (-(B * ⅟D))
                  (0 : Matrix β α R) (1 : Matrix β β R) *
                fromBlocks (1 : Matrix α α R) (B * ⅟D)
                  (0 : Matrix β α R) (1 : Matrix β β R)) *
              fromBlocks (A - B * ⅟D * C) (0 : Matrix α β R)
                (0 : Matrix β α R) D *
              (fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
                  (⅟D * C) (1 : Matrix β β R) *
                fromBlocks (1 : Matrix α α R) (0 : Matrix α β R)
                  (-(⅟D * C)) (1 : Matrix β β R)) := by
            simp [Matrix.mul_assoc]
          _ = fromBlocks (A - B * ⅟D * C) (0 : Matrix α β R)
                (0 : Matrix β α R) D := by
            rw [h_left_cancel, h_right_cancel]
            simp

end Schur22

private theorem isUnit_toBlocks₂₂_of_isUnit_entry
    {α : Type*} {R : Type*} [CommRing R]
    {M : Matrix (α ⊕ Fin 1) (α ⊕ Fin 1) R}
    (h : IsUnit (M (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)))) :
    IsUnit M.toBlocks₂₂ := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [Matrix.det_fin_one]
  have h_eq :
      M.toBlocks₂₂ (0 : Fin 1) (0 : Fin 1) =
        M (Sum.inr 0) (Sum.inr 0) := rfl
  rw [h_eq]
  exact h

section LocalFinOne

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Over a commutative local ring, every invertible matrix indexed by
a finite set `α` plus one distinguished coordinate admits elementary
left and right factors that make it block diagonal, with an invertible
`α` block and an invertible scalar block. The two block determinants
multiply to the determinant of the original matrix. -/
theorem exists_elementary_blockReduction_finOne
    (g : GL (α ⊕ Fin 1) R) :
    ∃ (eL eR : GL (α ⊕ Fin 1) R) (s : GL α R) (p : GL (Fin 1) R),
      eL ∈ elementarySubgroup (α ⊕ Fin 1) R ∧
        eR ∈ elementarySubgroup (α ⊕ Fin 1) R ∧
        eL * g * eR = BlockElementary.blockDiagonal s p ∧
        Matrix.GeneralLinearGroup.det s *
            Matrix.GeneralLinearGroup.det p =
          Matrix.GeneralLinearGroup.det g := by
  classical
  have h_nonempty : Nonempty (α ⊕ Fin 1) := ⟨Sum.inr 0⟩
  obtain ⟨e₀, he₀_mem, h_unit⟩ :=
    exists_elementary_mul_isUnit_entry
      (n := α ⊕ Fin 1) g (Sum.inr (0 : Fin 1))
  let g' : GL (α ⊕ Fin 1) R := e₀ * g
  have h_entry :
      IsUnit (g'.val (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1))) :=
    h_unit
  have h_isUnit_D : IsUnit g'.val.toBlocks₂₂ :=
    isUnit_toBlocks₂₂_of_isUnit_entry h_entry
  have hInvD : Invertible g'.val.toBlocks₂₂ :=
    h_isUnit_D.invertible
  let s : GL α R :=
    @schurComplement₂₂Unit α (Fin 1) _ _ _ _ R _ g' hInvD
  let p : GL (Fin 1) R :=
    @unitOfInvertible (Matrix (Fin 1) (Fin 1) R) _ g'.val.toBlocks₂₂ hInvD
  let eU : GL (α ⊕ Fin 1) R :=
    BlockElementary.upperUnit
      (-(g'.val.toBlocks₁₂ *
        @Invertible.invOf (Matrix (Fin 1) (Fin 1) R) _ _
          g'.val.toBlocks₂₂ hInvD))
  let eLw : GL (α ⊕ Fin 1) R :=
    BlockElementary.lowerUnit
      (-(@Invertible.invOf (Matrix (Fin 1) (Fin 1) R) _ _
            g'.val.toBlocks₂₂ hInvD *
          g'.val.toBlocks₂₁))
  have heU_mem : eU ∈ elementarySubgroup (α ⊕ Fin 1) R :=
    BlockElementary.upperUnit_mem_elementarySubgroup _
  have heLw_mem : eLw ∈ elementarySubgroup (α ⊕ Fin 1) R :=
    BlockElementary.lowerUnit_mem_elementarySubgroup _
  let eL : GL (α ⊕ Fin 1) R := eU * e₀
  let eR : GL (α ⊕ Fin 1) R := eLw
  have heL_mem : eL ∈ elementarySubgroup (α ⊕ Fin 1) R :=
    Subgroup.mul_mem _ heU_mem he₀_mem
  have heR_mem : eR ∈ elementarySubgroup (α ⊕ Fin 1) R := heLw_mem
  have h_block : eU * g' * eLw = BlockElementary.blockDiagonal s p := by
    have hSchur :=
      @upper_mul_mul_lower_eq_blockDiagonal_schur α (Fin 1) _ _ _ _ R _ g' hInvD
    simpa [s, p, eU, eLw] using hSchur
  have h_eL_g_eR : eL * g * eR = BlockElementary.blockDiagonal s p := by
    have h_assoc : eL * g * eR = eU * g' * eLw := by
      simp [eL, g', eR, mul_assoc]
    rw [h_assoc, h_block]
  have h_det_eL : Matrix.GeneralLinearGroup.det eL = 1 :=
    det_of_mem_elementarySubgroup heL_mem
  have h_det_eR : Matrix.GeneralLinearGroup.det eR = 1 :=
    det_of_mem_elementarySubgroup heR_mem
  have h_det_block :
      Matrix.GeneralLinearGroup.det (BlockElementary.blockDiagonal s p) =
        Matrix.GeneralLinearGroup.det s * Matrix.GeneralLinearGroup.det p :=
    BlockElementary.det_blockDiagonal s p
  have h_det_eq :
      Matrix.GeneralLinearGroup.det s *
          Matrix.GeneralLinearGroup.det p =
        Matrix.GeneralLinearGroup.det g := by
    calc
      Matrix.GeneralLinearGroup.det s *
            Matrix.GeneralLinearGroup.det p
        = Matrix.GeneralLinearGroup.det
            (BlockElementary.blockDiagonal s p) := h_det_block.symm
      _ = Matrix.GeneralLinearGroup.det (eL * g * eR) := by
          rw [h_eL_g_eR]
      _ = Matrix.GeneralLinearGroup.det eL *
            Matrix.GeneralLinearGroup.det g *
              Matrix.GeneralLinearGroup.det eR := by
          simp [map_mul, mul_assoc]
      _ = Matrix.GeneralLinearGroup.det g := by
          rw [h_det_eL, h_det_eR, one_mul, mul_one]
  exact ⟨eL, eR, s, p, heL_mem, heR_mem, h_eL_g_eR, h_det_eq⟩

end LocalFinOne

end Matrix.GeneralLinearGroup
