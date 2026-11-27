/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.LinearAlgebra.Matrix.DiagonalDominance
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

-- Singular, with negative off-diagonal entries: strict dominance is not needed.
example : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  apply Matrix.posSemidef_of_diagonallyDominant
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_two]

-- Empty matrices are included.
example (M : Matrix (Fin 0) (Fin 0) ℝ) : M.PosSemidef := by
  apply Matrix.posSemidef_of_diagonallyDominant
  · ext i; exact Fin.elim0 i
  · exact fun i => Fin.elim0 i

#print axioms Matrix.posSemidef_of_diagonallyDominant
