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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

variable {R : Type*} [CommRing R]

-- The diagonal has one variable, α 3, and degree two (not degree zero).
example (α : ℕ → R) :
    MvPolynomial.eval (fun t : Fin 1 => α (3 + t)) (MvPolynomial.hsymm (Fin 1) R 2) =
      α 3 ^ 2 := by
  rw [← alphaUpperEntry_eq_hsymm (α := α) (i := 2) (j := 2) (hij := by decide)]
  simp only [alphaUpperEntry.eq_1, alphaUpperEntry.eq_2, alphaUpperEntry_succ_succ]
  ring

-- Degree zero gives one, even when all variables are zero.
example :
    MvPolynomial.eval (fun _ : Fin 4 => (0 : ℤ)) (MvPolynomial.hsymm (Fin 4) ℤ 0) = 1 := by
  rw [← alphaUpperEntry_eq_hsymm (α := fun _ => 0) (i := 0) (j := 3) (hij := by decide),
    alphaUpperEntry.eq_1]

-- At positive degree the same zero substitution gives zero.
example :
    MvPolynomial.eval (fun _ : Fin 2 => (0 : ℤ)) (MvPolynomial.hsymm (Fin 2) ℤ 2) = 0 := by
  rw [← alphaUpperEntry_eq_hsymm (α := fun _ => 0) (i := 2) (j := 3) (hij := by decide)]
  simp only [alphaUpperEntry.eq_1, alphaUpperEntry.eq_2, alphaUpperEntry_succ_succ,
    zero_mul, add_zero, sub_self]

-- The two distinct variables must be α 3 and α 4; the mixed term occurs once.
example :
    MvPolynomial.eval (fun t : Fin 2 => ((3 + (t : ℕ) : ℕ) : ℤ))
      (MvPolynomial.hsymm (Fin 2) ℤ 2) = 37 := by
  rw [← alphaUpperEntry_eq_hsymm (α := fun k => (k : ℤ)) (i := 2) (j := 3)
    (hij := by decide)]
  norm_num [alphaUpperEntry.eq_1, alphaUpperEntry.eq_2, alphaUpperEntry_succ_succ]

end MetaMathlibExt

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
