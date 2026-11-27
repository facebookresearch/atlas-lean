/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition

/-! # Tests for the addition formula for Lucas sequences -/

namespace MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted

namespace two_mul_lucasU_add.Tests

open MetaMathlibExt

/-- The parameters $(P, Q) = (3, 2)$, for which $U_n = 2^n - 1$ and $V_n = 2^n + 1$. -/
def params32 : LucasSequenceParams := ⟨3, 2, by decide⟩

-- The terms used below: `U = 0, 1, 3, 7, 15, 31, …` and `V = 2, 3, 5, 9, 17, 33, …`.
example : lucasU params32 2 = 3 ∧ lucasU params32 3 = 7 ∧ lucasU params32 5 = 31 ∧
    lucasV params32 2 = 5 ∧ lucasV params32 3 = 9 := by
  decide

-- A concrete instance: `2 U_5 = U_2 V_3 + V_2 U_3`, that is `62 = 3 * 9 + 5 * 7`.
example : 2 * lucasU params32 (2 + 3) = 3 * 9 + 5 * 7 := by
  rw [two_mul_lucasU_add]
  decide

/-- The parameters $(P, Q) = (2, 1)$: the characteristic polynomial $x^2 - 2x + 1$ has the double
root $1$, so $U_n = n$ and $V_n = 2$. -/
def params21 : LucasSequenceParams := ⟨2, 1, by decide⟩

-- The formula needs no distinct roots: here it reads `2 * 9 = 4 * 2 + 2 * 5`.
example : 2 * lucasU params21 (4 + 5) = 4 * 2 + 2 * 5 := by
  rw [two_mul_lucasU_add]
  decide

-- For `n = 0` both sides reduce to `2 U_m`, since `U_0 = 0` and `V_0 = 2`.
example (params : LucasSequenceParams) (m : ℕ) :
    2 * lucasU params (m + 0) = lucasU params m * 2 + lucasV params m * 0 :=
  two_mul_lucasU_add params m 0

-- The Fibonacci specialization `2 F_{m+n} = F_m L_n + L_m F_n`, with `F` and `L` the Fibonacci
-- and Lucas numbers.
example (m n : ℕ) :
    2 * Nat.fib (m + n) = Nat.fib m * lucasNumber n + lucasNumber m * Nat.fib n := by
  have h := two_mul_lucasU_add fibonacciLucasParams m n
  simp only [lucasU_fibonacciLucasParams, lucasV_fibonacciLucasParams] at h
  exact_mod_cast h

end two_mul_lucasU_add.Tests

end MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted
