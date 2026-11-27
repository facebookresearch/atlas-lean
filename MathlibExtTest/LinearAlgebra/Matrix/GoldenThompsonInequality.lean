/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GoldenThompsonInequality

/-!
# Tests for the Golden–Thompson inequality

The inequality applies to two noncommuting Pauli matrices and to matrices of size zero.
-/

open scoped ComplexOrder
open MathlibExt.LinearAlgebra.Matrix.GoldenThompsonWanted

/-- The Pauli matrices Z and X are Hermitian and do not commute. -/
example :
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    (NormedSpace.exp (Z + X)).trace ≤ (NormedSpace.exp Z * NormedSpace.exp X).trace := by
  dsimp only
  apply golden_thompson <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- In dimension zero the statement requires no inhabitant of the index type. -/
example (A B : Matrix (Fin 0) (Fin 0) ℂ) :
    (NormedSpace.exp (A + B)).trace ≤ (NormedSpace.exp A * NormedSpace.exp B).trace :=
  golden_thompson (Subsingleton.elim _ _) (Subsingleton.elim _ _)
