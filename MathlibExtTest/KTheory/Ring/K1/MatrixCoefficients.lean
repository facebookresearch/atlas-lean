/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.KTheory.Ring.K1.Basic

/-! # A finite-rank coefficient map into a noncommutative matrix ring -/

open AlgebraicKTheory

private abbrev R := ZMod 3
private abbrev S := Matrix (Fin 2) (Fin 2) R

private def intoMatrices : R →+* S := Matrix.scalar (Fin 2)

private def negativeUnit : Matrix.GeneralLinearGroup (Fin 1) R :=
  Matrix.GeneralLinearGroup.scalar (Fin 1) (-1 : Rˣ)

private def negativeScalarMatrix : Matrix.GeneralLinearGroup (Fin 1) S :=
  Matrix.GeneralLinearGroup.scalar (Fin 1) (-1 : Sˣ)

/-- Coefficient extension sends the one-by-one negative unit to the negative scalar matrix. -/
example : K1.mapRingHom intoMatrices (K1.mk negativeUnit) = K1.mk negativeScalarMatrix := by
  rw [K1.mapRingHom_mk]
  congr 1
  apply Units.ext
  ext i j a b
  fin_cases i
  fin_cases j
  simp [negativeUnit, negativeScalarMatrix, intoMatrices, Matrix.GeneralLinearGroup.scalar,
    Matrix.diagonal_apply, Matrix.one_apply, Matrix.neg_apply]
  split <;> simp_all

/-- The finite representative on the target side is not the identity matrix. -/
example : negativeScalarMatrix ≠ 1 := by
  intro h
  have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 1) S => g.val 0 0 0 0) h
  have h' : (-1 : R) = 1 := by
    simpa [negativeScalarMatrix, Matrix.GeneralLinearGroup.scalar] using he
  exact (by decide : (-1 : R) ≠ 1) h'
