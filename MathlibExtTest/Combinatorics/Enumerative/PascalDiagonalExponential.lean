/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PascalDiagonalExponential
import Mathlib.Tactic.NormNum

open scoped Matrix
open MetaMathlibExt

-- The exponential is the empty identity in dimension zero.
example : NormedSpace.exp (pascalDiagonalMatrix 2 0) = 1 := by
  rw [exp_pascalDiagonalMatrix 2 (by decide) 0]
  exact Subsingleton.elim _ _

-- With k = 1, the formula gives the usual Pascal entry on the second subdiagonal.
example : NormedSpace.exp (pascalDiagonalMatrix 1 4) (3 : Fin 4) (1 : Fin 4) = 3 := by
  have hα : pascalExpFirstColumn 1 3 = 1 := by
    norm_num [pascalExpFirstColumn_of_lt (k := 1) (i := 3) (by decide) (by decide),
      pascalExpFirstColumn_of_lt (k := 1) (i := 2) (by decide) (by decide), pascalExpFirstColumn_one]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 3 1)
    (exp_pascalDiagonalMatrix 1 (by decide) 4)
  norm_num [Matrix.hadamard_apply, Matrix.sum_apply, Finset.sum_range_succ, pascalDiagonalMatrix,
    Nat.choose, hα] at h
  exact h

-- The second power contributes on subdiagonal 4, with first-column coefficient 3.
example : NormedSpace.exp (pascalDiagonalMatrix 2 6) (5 : Fin 6) (1 : Fin 6) = 15 := by
  have hα : pascalExpFirstColumn 2 5 = 3 := by
    norm_num [pascalExpFirstColumn_of_lt (k := 2) (i := 5) (by decide) (by decide),
      pascalExpFirstColumn_of_lt (k := 2) (i := 3) (by decide) (by decide), pascalExpFirstColumn_one,
      Nat.choose]
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 5 1)
    (exp_pascalDiagonalMatrix 2 (by decide) 6)
  norm_num [Matrix.hadamard_apply, Matrix.sum_apply, Finset.sum_range_succ, pascalDiagonalMatrix,
    Nat.choose, hα] at h
  exact h

-- The odd subdiagonals vanish for k = 2.
example : NormedSpace.exp (pascalDiagonalMatrix 2 6) (4 : Fin 6) (1 : Fin 6) = 0 := by
  simpa [Matrix.hadamard_apply, Matrix.sum_apply, Finset.sum_range_succ, pascalDiagonalMatrix]
    using congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 4 1)
      (exp_pascalDiagonalMatrix 2 (by decide) 6)
