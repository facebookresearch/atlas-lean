/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Rat.Defs

/-!
# Integer sequences `P(n) F_n + Q(n) F_{n-1}` with rational polynomial coefficients

Statements from Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4.

The paper uses `F_{-1} = 1`. To stay inside `Nat.fib`, every occurrence of `F_{n-1}`
is written as `F_{n+1} - F_n`, which agrees with the paper for all `n ≥ 0`
(including `n = 0`). A sequence is an *integer sequence* when every term `w_n`,
`n ≥ 0`, is an integer. The paper's nondegeneracy assumptions on the leading
coefficients (`a ≠ 0`, `d ≠ 0`) are dropped: the equivalences hold for all rational
coefficients.

The coefficient formulas (2.10) and (2.15) survive in the extracted text with their
numerators only; the denominators used here are the unique ones for which the
displayed numerators solve the paper's initial-value systems (2.8) and (2.13), and
they reproduce the paper's worked examples. In Theorem 3.1 the extracted formulas
for `c` and `d` contradict the paper's own example; the stated reading is the one
that the example and the initial-value system support (see the source audit table).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The rational sequence `w_n = (a n + b) F_n + (c n + d) F_{n-1}` is an integer
sequence if and only if `d` is an integer and
`a = (-z₁ - 3 z₂ + 2 z₃) / 5`, `b = (6 z₁ + 3 z₂ - 2 z₃) / 5`,
`c = (-2 z₁ + 4 z₂ - z₃) / 5` for some integers `z₁, z₂, z₃` (then `z₁ = w₁`,
`z₂ = w₂ - d`, `z₃ = w₃ - d`). Here `F_{n-1}` is written as `F_{n+1} - F_n`.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 2.1 (`fq-2024-szakacs06212024rev-thm-2.1`). -/
public theorem_wanted fib_linear_coeff_isInt_iff (a b c d : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n + b) * Nat.fib n + (c * n + d) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)) ↔
    (∃ k : ℤ, (k : ℚ) = d) ∧ ∃ z₁ z₂ z₃ : ℤ,
      a = ((-z₁ - 3 * z₂ + 2 * z₃ : ℤ) : ℚ) / 5 ∧
      b = ((6 * z₁ + 3 * z₂ - 2 * z₃ : ℤ) : ℚ) / 5 ∧
      c = ((-2 * z₁ + 4 * z₂ - z₃ : ℤ) : ℚ) / 5

/-- The rational sequence `w_n = (a n² + b n + c) F_n + (d n² + e n + f) F_{n-1}` is
an integer sequence if and only if `f` is an integer and, for some integers
`z₁, …, z₅` (then `z₁ = w₁`, `z₂ = w₂ - f`, `z₃ = w₃ - f`, `z₄ = w₄ - 2f`,
`z₅ = w₅ - 3f`), the coefficients are given by formula (2.10):
`a = (-z₁ + 3z₂ + z₃ - 3z₄ + z₅) / 10`,
`b = (-5z₁ - 75z₂ + 15z₃ + 45z₄ - 17z₅) / 50`,
`c = (30z₁ + 30z₂ - 10z₃ - 15z₄ + 6z₅) / 25`,
`d = (3z₁ - 4z₂ - 3z₃ + 4z₄ - z₅) / 10`,
`e = (-45z₁ + 80z₂ + 15z₃ - 40z₄ + 11z₅) / 50`.
Here `F_{n-1}` is written as `F_{n+1} - F_n`.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 2.2 (`fq-2024-szakacs06212024rev-thm-2.2`). -/
public theorem_wanted fib_quadratic_coeff_isInt_iff (a b c d e f : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n ^ 2 + b * n + c) * Nat.fib n +
        (d * n ^ 2 + e * n + f) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)) ↔
    (∃ k : ℤ, (k : ℚ) = f) ∧ ∃ z₁ z₂ z₃ z₄ z₅ : ℤ,
      a = ((-z₁ + 3 * z₂ + z₃ - 3 * z₄ + z₅ : ℤ) : ℚ) / 10 ∧
      b = ((-5 * z₁ - 75 * z₂ + 15 * z₃ + 45 * z₄ - 17 * z₅ : ℤ) : ℚ) / 50 ∧
      c = ((30 * z₁ + 30 * z₂ - 10 * z₃ - 15 * z₄ + 6 * z₅ : ℤ) : ℚ) / 25 ∧
      d = ((3 * z₁ - 4 * z₂ - 3 * z₃ + 4 * z₄ - z₅ : ℤ) : ℚ) / 10 ∧
      e = ((-45 * z₁ + 80 * z₂ + 15 * z₃ - 40 * z₄ + 11 * z₅ : ℤ) : ℚ) / 50

/-- The rational sequence `w_n = (a n² + b n + c) F_n + (d n + e) F_{n-1}` is an
integer sequence if and only if `e` is an integer and, for some integers
`z₁, …, z₄` (then `z₁ = w₁`, `z₂ = w₂ - e`, `z₃ = w₃ - e`, `z₄ = w₄ - 2e`), the
coefficients are given by formula (2.15):
`a = (2z₁ - z₂ - 2z₃ + z₄) / 10`, `b = (-56z₁ - 7z₂ + 66z₃ - 23z₄) / 50`,
`c = (48z₁ + 6z₂ - 28z₃ + 9z₄) / 25`, `d = (-6z₁ + 18z₂ - 9z₃ + 2z₄) / 25`.
Here `F_{n-1}` is written as `F_{n+1} - F_n`.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 2.3 (`fq-2024-szakacs06212024rev-thm-2.3`). -/
public theorem_wanted fib_quadratic_linear_coeff_isInt_iff (a b c d e : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n ^ 2 + b * n + c) * Nat.fib n +
        (d * n + e) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)) ↔
    (∃ k : ℤ, (k : ℚ) = e) ∧ ∃ z₁ z₂ z₃ z₄ : ℤ,
      a = ((2 * z₁ - z₂ - 2 * z₃ + z₄ : ℤ) : ℚ) / 10 ∧
      b = ((-56 * z₁ - 7 * z₂ + 66 * z₃ - 23 * z₄ : ℤ) : ℚ) / 50 ∧
      c = ((48 * z₁ + 6 * z₂ - 28 * z₃ + 9 * z₄ : ℤ) : ℚ) / 25 ∧
      d = ((-6 * z₁ + 18 * z₂ - 9 * z₃ + 2 * z₄ : ℤ) : ℚ) / 25

/-- The rational sequence `w_n = (a n + b) F_n + (c n + d) F_{n-1} + e + f (-1)^n` is
an integer sequence if and only if there are integers `w₀, …, w₅` (its initial
values) with
`a = (3w₀ + 2w₁ - 7w₂ - w₃ + 4w₄ - w₅) / 5`,
`b = (-3w₀ - 2w₁ - 3w₂ + 6w₃ + 6w₄ - 4w₅) / 5`,
`c = (-4w₀ - w₁ + 11w₂ - 2w₃ - 7w₄ + 3w₅) / 5`,
`d = -2w₁ + w₂ + 2w₃ - w₄`,
`e = (w₀ + 3w₁ + w₂ - 3w₃ - w₄ + w₅) / 2`,
`f = (w₀ + w₁ - 3w₂ - w₃ + 3w₄ - w₅) / 2`.
The extracted text prints `-3w₅` in `c` and `2w₁` in `d`; those versions contradict
the paper's example `w = (0, 1, 2, 6, 12, 26)`, `c = 3/5`, `d = 0`. Here `F_{n-1}`
is written as `F_{n+1} - F_n`.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 3.1 (`fq-2024-szakacs06212024rev-thm-3.1`). -/
public theorem_wanted fib_linear_coeff_add_alternating_isInt_iff (a b c d e f : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n + b) * Nat.fib n + (c * n + d) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) +
        e + f * (-1) ^ n) ↔
    ∃ w₀ w₁ w₂ w₃ w₄ w₅ : ℤ,
      a = ((3 * w₀ + 2 * w₁ - 7 * w₂ - w₃ + 4 * w₄ - w₅ : ℤ) : ℚ) / 5 ∧
      b = ((-3 * w₀ - 2 * w₁ - 3 * w₂ + 6 * w₃ + 6 * w₄ - 4 * w₅ : ℤ) : ℚ) / 5 ∧
      c = ((-4 * w₀ - w₁ + 11 * w₂ - 2 * w₃ - 7 * w₄ + 3 * w₅ : ℤ) : ℚ) / 5 ∧
      d = ((-2 * w₁ + w₂ + 2 * w₃ - w₄ : ℤ) : ℚ) ∧
      e = ((w₀ + 3 * w₁ + w₂ - 3 * w₃ - w₄ + w₅ : ℤ) : ℚ) / 2 ∧
      f = ((w₀ + w₁ - 3 * w₂ - w₃ + 3 * w₄ - w₅ : ℤ) : ℚ) / 2

end

end MetaMathlibExt
