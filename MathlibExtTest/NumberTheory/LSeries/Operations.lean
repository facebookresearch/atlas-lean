/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.Operations

import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Tests for operations on `L`-series

Values of `ArithmeticFunction.squareLift` at squares, non-squares and the boundary `0`, `1`, its
multiplicativity, and the shift `L(f · n^a, s) = L(f, s - a)`.
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace OperationsTest

example (f : ArithmeticFunction ℤ) : f.squareLift 9 = f 3 := by
  simpa using f.squareLift_apply_sq 3

example (f : ArithmeticFunction ℤ) : f.squareLift 1 = f 1 := by
  simpa using f.squareLift_apply_sq 1

example (f : ArithmeticFunction ℤ) : f.squareLift 0 = 0 := by simp

example (f : ArithmeticFunction ℤ) : f.squareLift 2 = 0 :=
  f.squareLift_apply_of_not_isSquare (by
    rintro ⟨r, hr⟩
    have : r ≤ 1 := by nlinarith
    interval_cases r <;> omega)

example (f : ArithmeticFunction ℤ) : f.squareLift 12 = 0 :=
  f.squareLift_apply_of_not_isSquare (by
    rintro ⟨r, hr⟩
    have : r ≤ 3 := by nlinarith
    interval_cases r <;> omega)

/-- The square lift of `ζ` is the indicator of the squares. -/
example : (ζ : ArithmeticFunction ℕ).squareLift 16 = 1 := by
  rw [show (16 : ℕ) = 4 ^ 2 by norm_num, squareLift_apply_sq]
  simp

example : (ζ : ArithmeticFunction ℕ).squareLift.IsMultiplicative :=
  isMultiplicative_zeta.squareLift

example : Nat.Coprime 4 9 → (IsSquare (4 * 9) ↔ IsSquare 4 ∧ IsSquare 9) :=
  Nat.Coprime.isSquare_mul_iff

/-- `L(squareLift f, s) = L(f, 2s)`. -/
example (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeries (fun n => f.squareLift n) s = LSeries (fun n => f n) (2 * s) :=
  LSeries_squareLift f s

/-- `∑ n^a n^{-s} = ζ(s - a)`; at `a = 1`, `s = 3`, this is `ζ(2)`. -/
example : LSeries (fun n : ℕ => (n : ℂ) ^ (1 : ℂ)) 3 = riemannZeta 2 := by
  rw [LSeries_cpow_eq_riemannZeta (by norm_num)]
  norm_num

/-- The boundary of absolute convergence: `∑ n^a n^{-s}` diverges at `re (s - a) = 1`. -/
example : ¬ LSeriesSummable (fun n : ℕ => (n : ℂ) ^ (1 : ℂ)) 2 := by
  rw [LSeriesSummable_cpow_iff]
  norm_num

end OperationsTest
