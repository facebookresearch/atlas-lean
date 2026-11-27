/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ShiftedAlphaStirlingMatrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- A nonnormalized first entry is allowed in the factorization. The final
-- entry also exercises the shift from a zero-based column index to α 3.
example : shiftedAlphaStirlingMatrix (fun j : ℕ => (j : ℤ) + 1) 3 =
    !![2, 2, 2; 2, 8, 16; 2, 26, 90] := by
  rw [shiftedAlphaStirlingMatrix_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, alphaStirlingMatrix, alphaUpperMatrix,
      alphaStirlingEntry.eq_1, alphaStirlingEntry.eq_2, alphaStirlingEntry_succ_succ,
      alphaUpperEntry.eq_1, alphaUpperEntry.eq_2, alphaUpperEntry_succ_succ]

-- Over a ring with zero divisors, there is no cancellation by α 2.
example (α : ℕ → ℤ × ℤ) (hα : α 1 = 1) :
    (shiftedAlphaStirlingMatrix α 3).det = α 2 * α 3 ^ 2 := by
  simp [det_shiftedAlphaStirlingMatrix, hα, Fin.prod_univ_three]

example (α : ℕ → ℤ) (hα : α 1 = 1) : (shiftedAlphaStirlingMatrix α 0).det = 1 := by
  simp [det_shiftedAlphaStirlingMatrix, hα]

end MetaMathlibExt
