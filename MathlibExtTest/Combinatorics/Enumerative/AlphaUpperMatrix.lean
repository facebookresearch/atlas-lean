/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlphaUpperMatrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace MetaMathlibExt.det_alphaUpperMatrix

variable {R : Type*} [CommRing R]

-- Check the shifted sequence indices and the first nontrivial subdiagonal cancellation.
example (α : ℕ → R) :
    alphaUpperMatrix α 3 = !![1, 1, 1; 0, α 2, α 2 + α 3; 0, 0, α 3 ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaUpperMatrix, alphaUpperEntry.eq_1, alphaUpperEntry.eq_2,
      alphaUpperEntry_succ_succ]
  all_goals ring

example (α : ℕ → R) : (alphaUpperMatrix α 0).det = 1 := by
  simp [det_alphaUpperMatrix]

example (α : ℕ → R) : (alphaUpperMatrix α 3).det = α 2 * α 3 ^ 2 := by
  simp [det_alphaUpperMatrix, Fin.prod_univ_three]

end MetaMathlibExt.det_alphaUpperMatrix
