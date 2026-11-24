/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeRowCore
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic

/-!
# Checks for block-compatible row automorphisms

The coefficient ring `Matrix (Fin 2) (Fin 2) ℤ` detects multiplication order
and distinguishes row multiplication from the incorrect column action on a
left module.  The remaining checks cover rank zero, an empty identity block,
a zero ring, and successor stabilization.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits FGProjectiveCat
open scoped Matrix

universe u

private abbrev Coefficients := Matrix (Fin 2) (Fin 2) ℤ

private def upperUnit : Coefficientsˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private def lowerUnit : Coefficientsˣ where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private def rankOneUnit (g : Coefficientsˣ) :
    Matrix.GeneralLinearGroup (Fin 1) Coefficients :=
  Units.map (Matrix.scalar (Fin 1)).toMonoidHom g

-- These units do not commute in the coefficient ring.
example : (upperUnit : Coefficients) * (lowerUnit : Coefficients) ≠
    (lowerUnit : Coefficients) * (upperUnit : Coefficients) := by
  intro h
  have h00 := congrArg (fun A : Coefficients => A 0 0) h
  norm_num [upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two] at h00

-- The left-module map multiplies the input coefficient on its right.
example :
    (finiteOppositeGLAutRowMulEquiv Coefficients 1
      (MulOpposite.op (rankOneUnit upperUnit))).asIso.hom
        (fun _ => (lowerUnit : Coefficients)) 0 =
      (lowerUnit : Coefficients) * (upperUnit : Coefficients) := by
  rw [finiteOppositeGLAutRowMulEquiv_apply]
  simp [rankOneUnit, Matrix.vecMul, dotProduct]

-- Opposite-group multiplication and endomorphism composition reverse the
-- product of these two noncommuting matrix coefficients.
example :
    (finiteOppositeGLAutRowMulEquiv Coefficients 1
      (MulOpposite.op (rankOneUnit upperUnit) *
        MulOpposite.op (rankOneUnit lowerUnit))).asIso.hom (fun _ => 1) 0 =
      (lowerUnit : Coefficients) * (upperUnit : Coefficients) := by
  rw [finiteOppositeGLAutRowMulEquiv_apply]
  simp [rankOneUnit, Matrix.vecMul, Matrix.mul_apply, dotProduct]

-- The action on a rank-zero free module is the unique automorphism.
example (R : Type u) [Ring R]
    (g : (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ) :
    finiteOppositeGLAutRowMulEquiv R 0 g = Aut.of (Iso.refl (standardFree R 0)) := by
  apply Aut.ext
  apply Iso.ext
  apply FGProjectiveCat.hom_ext
  ext v i
  exact i.elim0

-- The full block theorem includes an empty first block.
example (R : Type u) [Ring R] (m : ℕ)
    (h : Matrix.GeneralLinearGroup (Fin m) R) :
    finiteOppositeGLAutRowMulEquiv R (0 + m)
        (MulOpposite.op
          (Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := 0) (n := m))
            (Matrix.GeneralLinearGroup.BlockElementary.blockDiagonal
              (1 : Matrix.GeneralLinearGroup (Fin 0) R) h))) =
      (standardFreeAddIso R 0 m).symm.conjAut
        (Aut.of (biprod.mapIso (Iso.refl (standardFree R 0))
          (finiteOppositeGLAutRowMulEquiv R m (MulOpposite.op h)).asIso)) := by
  have hone : (1 : Aut (standardFree R 0)).asIso = Iso.refl (standardFree R 0) := rfl
  simpa only [MulOpposite.op_one, map_one, hone] using
    finiteOppositeGLAutRowMulEquiv_blockDiagonal R 0 m 1 h

-- The empty identity block preserves the original matrix and automorphism.
example (R : Type u) [Ring R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g) =
      (standardFreeAddIso R n 0).symm.conjAut
        (Aut.of (biprod.mapIso
          (finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso
          (Iso.refl (standardFree R 0)))) := by
  simpa only [Nat.add_zero, Matrix.GeneralLinearGroup.blockStabilization_zero] using
    finiteOppositeGLAutRowMulEquiv_blockStabilization R n 0 g

-- A zero ring is allowed in every rank, with no nontriviality assumption.
example (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) (ZMod 1))ᵐᵒᵖ) :
    finiteOppositeGLAutRowMulEquiv (ZMod 1) n g =
      Aut.of (Iso.refl (standardFree (ZMod 1) n)) := by
  apply Aut.ext
  apply Iso.ext
  apply FGProjectiveCat.hom_ext
  ext v i
  exact Subsingleton.elim _ _

-- Successor stabilization works over the noncommutative coefficient ring.
example (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) Coefficients) :
    finiteOppositeGLAutRowMulEquiv Coefficients (n + 1)
        (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization Coefficients g)) =
      (standardFreeAddIso Coefficients n 1).symm.conjAut
        (Aut.of (biprod.mapIso
          (finiteOppositeGLAutRowMulEquiv Coefficients n (MulOpposite.op g)).asIso
          (Iso.refl (standardFree Coefficients 1)))) :=
  finiteOppositeGLAutRowMulEquiv_stabilization Coefficients n g

#print axioms FGProjectiveCat.rowGLLinearEquiv
#print axioms FGProjectiveCat.rowGLLinearEquiv_apply
#print axioms FGProjectiveCat.finiteOppositeGLAutRowMulEquiv
#print axioms FGProjectiveCat.finiteOppositeGLAutRowMulEquiv_apply
#print axioms FGProjectiveCat.finiteOppositeGLAutRowMulEquiv_blockDiagonal
#print axioms FGProjectiveCat.finiteOppositeGLAutRowMulEquiv_blockStabilization
#print axioms FGProjectiveCat.finiteOppositeGLAutRowMulEquiv_stabilization

end
