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
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite Whitehead block factorization

`diag(g,g⁻¹)` is a product of six block unipotents, hence lies in `E_{n⊕n}`;
the same yields `diag(⁅g,h⁆,1)` and the reindexed `Fin (n+n)` form over an
arbitrary (possibly noncommutative) ring.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix
open scoped commutatorElement

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [Ring R]

/-- Diagonal unit `diag(g,g⁻¹)` on `n ⊕ n`. -/
def diagUnit (g : GL n R) : GL (n ⊕ n) R where
  val := fromBlocks (↑g : Matrix n n R) 0 0 (↑(g⁻¹) : Matrix n n R)
  inv := fromBlocks (↑(g⁻¹) : Matrix n n R) 0 0 (↑g : Matrix n n R)
  val_inv := by
    have h1 : (↑g : Matrix n n R) * (↑(g⁻¹) : Matrix n n R) = 1 := by
      have := g.val_inv
      exact_mod_cast this
    have h2 : (↑(g⁻¹) : Matrix n n R) * (↑g : Matrix n n R) = 1 := by
      have := g.inv_val
      exact_mod_cast this
    rw [fromBlocks_multiply]
    simp [h1, h2]
  inv_val := by
    have h1 : (↑g : Matrix n n R) * (↑(g⁻¹) : Matrix n n R) = 1 := by
      have := g.val_inv
      exact_mod_cast this
    have h2 : (↑(g⁻¹) : Matrix n n R) * (↑g : Matrix n n R) = 1 := by
      have := g.inv_val
      exact_mod_cast this
    rw [fromBlocks_multiply]
    simp [h1, h2]

@[simp]
lemma coe_diagUnit (g : GL n R) :
    (↑(diagUnit (n := n) (R := R) g) : Matrix (n ⊕ n) (n ⊕ n) R) =
      fromBlocks (↑g : Matrix n n R) 0 0 (↑(g⁻¹) : Matrix n n R) := rfl

/-! ### Six-unipotent Whitehead identity -/

private lemma diagUnit_val_mul_inv (g : GL n R) :
    (↑g : Matrix n n R) * (↑(g⁻¹) : Matrix n n R) = 1 := by
  have := g.val_inv
  exact_mod_cast this

private lemma diagUnit_inv_mul_val (g : GL n R) :
    (↑(g⁻¹) : Matrix n n R) * (↑g : Matrix n n R) = 1 := by
  have := g.inv_val
  exact_mod_cast this

/-- Whitehead identity `U(g) L(-g⁻¹) U(g) U(-1) L(1) U(-1) = diagUnit g`. -/
theorem diagUnit_eq_six_unipotent (g : GL n R) :
    BlockElementary.upperUnit (↑g : Matrix n n R) *
      BlockElementary.lowerUnit (-(↑(g⁻¹) : Matrix n n R)) *
      BlockElementary.upperUnit (↑g : Matrix n n R) *
      BlockElementary.upperUnit (-1 : Matrix n n R) *
      BlockElementary.lowerUnit (1 : Matrix n n R) *
      BlockElementary.upperUnit (-1 : Matrix n n R) = diagUnit g := by
  apply Units.ext
  have h1 := diagUnit_val_mul_inv g
  have h2 := diagUnit_inv_mul_val g
  simp only [BlockElementary.coe_upperUnit, BlockElementary.coe_lowerUnit, coe_diagUnit,
    Units.val_mul]
  have s1 :
      fromBlocks (1 : Matrix n n R) (↑g : Matrix n n R) (0 : Matrix n n R) 1 *
        fromBlocks (1 : Matrix n n R) (0 : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R)) 1 =
      fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R)) 1 := by
    rw [fromBlocks_multiply]
    simp [h1]
  have s2 :
      fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R)) 1 *
        fromBlocks (1 : Matrix n n R) (↑g : Matrix n n R) (0 : Matrix n n R) 1 =
      fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R)) 0 := by
    rw [fromBlocks_multiply]
    simp [h2]
  have s3 :
      fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R)) 0 *
        fromBlocks (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R) 1 =
      fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R))
        (↑(g⁻¹) : Matrix n n R) := by
    rw [fromBlocks_multiply]
    simp
  have s4 :
      fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R))
          (↑(g⁻¹) : Matrix n n R) *
        fromBlocks (1 : Matrix n n R) (0 : Matrix n n R) (1 : Matrix n n R) 1 =
      fromBlocks (↑g : Matrix n n R) (↑g : Matrix n n R) (0 : Matrix n n R)
        (↑(g⁻¹) : Matrix n n R) := by
    rw [fromBlocks_multiply]
    simp
  have s5 :
      fromBlocks (↑g : Matrix n n R) (↑g : Matrix n n R) (0 : Matrix n n R)
          (↑(g⁻¹) : Matrix n n R) *
        fromBlocks (1 : Matrix n n R) (-1 : Matrix n n R) (0 : Matrix n n R) 1 =
      fromBlocks (↑g : Matrix n n R) (0 : Matrix n n R) (0 : Matrix n n R)
        (↑(g⁻¹) : Matrix n n R) := by
    rw [fromBlocks_multiply]
    simp
  calc
    fromBlocks (1 : Matrix n n R) (↑g : Matrix n n R) 0 1 *
        fromBlocks 1 0 (-(↑(g⁻¹) : Matrix n n R)) 1 *
        fromBlocks 1 (↑g : Matrix n n R) 0 1 *
        fromBlocks 1 (-1 : Matrix n n R) 0 1 *
        fromBlocks 1 0 (1 : Matrix n n R) 1 *
        fromBlocks 1 (-1 : Matrix n n R) 0 1
        = (fromBlocks (1 : Matrix n n R) (↑g : Matrix n n R) 0 1 *
          fromBlocks 1 0 (-(↑(g⁻¹) : Matrix n n R)) 1 *
          fromBlocks 1 (↑g : Matrix n n R) 0 1 *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 *
          fromBlocks 1 0 (1 : Matrix n n R) 1) *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 := by
          simp only [Matrix.mul_assoc]
    _ = (fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R)) 1 *
          fromBlocks 1 (↑g : Matrix n n R) 0 1 *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 *
          fromBlocks 1 0 (1 : Matrix n n R) 1) *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 := by
          rw [s1]
    _ = (fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R)) 0 *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 *
          fromBlocks 1 0 (1 : Matrix n n R) 1) *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 := by
          rw [s2, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (fromBlocks (0 : Matrix n n R) (↑g : Matrix n n R) (-(↑(g⁻¹) : Matrix n n R))
            (↑(g⁻¹) : Matrix n n R) *
          fromBlocks 1 0 (1 : Matrix n n R) 1) *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 := by
          rw [s3, Matrix.mul_assoc]
    _ = fromBlocks (↑g : Matrix n n R) (↑g : Matrix n n R) 0 (↑(g⁻¹) : Matrix n n R) *
          fromBlocks 1 (-1 : Matrix n n R) 0 1 := by
          rw [s4]
    _ = fromBlocks (↑g : Matrix n n R) 0 0 (↑(g⁻¹) : Matrix n n R) := s5

theorem diagUnit_mem (g : GL n R) :
    diagUnit g ∈ elementarySubgroup (n ⊕ n) R := by
  rw [← diagUnit_eq_six_unipotent g]
  have hg : BlockElementary.upperUnit (↑g : Matrix n n R) ∈ elementarySubgroup (n ⊕ n) R :=
    BlockElementary.upperUnit_mem_elementarySubgroup _
  have hg_inv : BlockElementary.lowerUnit (-(↑(g⁻¹) : Matrix n n R)) ∈
      elementarySubgroup (n ⊕ n) R :=
    BlockElementary.lowerUnit_mem_elementarySubgroup _
  have h_m1 : BlockElementary.upperUnit (-1 : Matrix n n R) ∈ elementarySubgroup (n ⊕ n) R :=
    BlockElementary.upperUnit_mem_elementarySubgroup _
  have h1 : BlockElementary.lowerUnit (1 : Matrix n n R) ∈ elementarySubgroup (n ⊕ n) R :=
    BlockElementary.lowerUnit_mem_elementarySubgroup _
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hg_inv) hg) h_m1) h1) h_m1

/-! ### Commutator `diag(⁅g,h⁆,1)` -/

/-- `diag(⁅g,h⁆,1)` equals `diagUnit g * diagUnit h * diagUnit (g⁻¹*h⁻¹)`. -/
theorem diagUnit_commutator_eq (g h : GL n R) :
    diagUnit g * diagUnit h * diagUnit (g⁻¹ * h⁻¹) =
      blockDiagonalOne n n R ⁅g, h⁆ := by
  apply Units.ext
  simp only [coe_diagUnit, coe_blockDiagonalOne, Units.val_mul, fromBlocks_multiply,
    mul_zero, zero_mul, add_zero, zero_add]
  have h_comm : g * h * (g⁻¹ * h⁻¹) = ⁅g, h⁆ := by
    simp [commutatorElement_def, mul_assoc]
  have hg_top : (↑g : Matrix n n R) * (↑h : Matrix n n R) *
      ((↑(g⁻¹) : Matrix n n R) * (↑(h⁻¹) : Matrix n n R)) =
      ↑(⁅g, h⁆ : GL n R) := by
    calc
      (↑g : Matrix n n R) * (↑h : Matrix n n R) *
          ((↑(g⁻¹) : Matrix n n R) * (↑(h⁻¹) : Matrix n n R))
          = ↑(g * h * (g⁻¹ * h⁻¹)) := by
            simp [Units.val_mul, mul_assoc]
      _ = ↑(⁅g, h⁆ : GL n R) := by rw [h_comm]
  have h_inv : (g⁻¹ * h⁻¹)⁻¹ = h * g := by
    simp
  have h2_h := diagUnit_inv_mul_val h
  have h2_g := diagUnit_inv_mul_val g
  have hg_bot : (↑(g⁻¹) : Matrix n n R) * (↑(h⁻¹) : Matrix n n R) *
        (↑((g⁻¹ * h⁻¹)⁻¹) : Matrix n n R) = 1 := by
    calc
      (↑(g⁻¹) : Matrix n n R) * (↑(h⁻¹) : Matrix n n R) * (↑((g⁻¹ * h⁻¹)⁻¹) : Matrix n n R)
          = (↑(g⁻¹) : Matrix n n R) * (↑(h⁻¹) : Matrix n n R) * (↑(h * g) : Matrix n n R) := by
            rw [h_inv]
      _ = (↑(g⁻¹) : Matrix n n R) *
          ((↑(h⁻¹) : Matrix n n R) * (↑h : Matrix n n R) *
            (↑g : Matrix n n R)) := by
            simp [Units.val_mul, mul_assoc]
      _ = (↑(g⁻¹) : Matrix n n R) * (↑g : Matrix n n R) := by
            simp [h2_h]
      _ = 1 := h2_g
  rw [hg_top, hg_bot]

theorem diag_commutator_mem (g h : GL n R) :
    blockDiagonalOne n n R ⁅g, h⁆ ∈ elementarySubgroup (n ⊕ n) R := by
  rw [← diagUnit_commutator_eq g h]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (diagUnit_mem g) (diagUnit_mem h))
    (diagUnit_mem (g⁻¹ * h⁻¹))

/-! ### `Fin (n+n)` reindexed commutator -/

/-- Reindexed `diag(⁅g,h⁆,1)` in `GL (Fin (k+k))`. -/
def reindexedDiagCommutatorUnit (k : ℕ) (R : Type*) [Ring R]
    (g h : GL (Fin k) R) : GL (Fin (k + k)) R :=
  reindexMulEquiv (finSumFinEquiv (m := k) (n := k))
    (blockDiagonalOne (Fin k) (Fin k) R ⁅g, h⁆)

theorem reindexedDiagCommutatorUnit_mem (k : ℕ) (R : Type*) [Ring R]
    (g h : GL (Fin k) R) :
    reindexedDiagCommutatorUnit k R g h ∈ elementarySubgroup (Fin (k + k)) R :=
  reindexMulEquiv_mem_elementarySubgroup _ (diag_commutator_mem g h)

@[simp]
theorem coe_reindexedDiagCommutatorUnit (k : ℕ) (R : Type*) [Ring R]
    (g h : GL (Fin k) R) :
    (↑(reindexedDiagCommutatorUnit k R g h) : Matrix (Fin (k + k)) (Fin (k + k)) R) =
      Matrix.reindex (finSumFinEquiv (m := k) (n := k)) (finSumFinEquiv (m := k) (n := k))
        (fromBlocks (↑(⁅g, h⁆ : GL (Fin k) R) : Matrix (Fin k) (Fin k) R) 0 0 1) := by
  simp only [reindexedDiagCommutatorUnit, coe_reindexMulEquiv, coe_blockDiagonalOne]

end Matrix.GeneralLinearGroup
