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

/-- **Integer sequences with linear Fibonacci coefficients.** Let $F_n$ be the $n$-th Fibonacci
number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every $n \ge 0$. For rational
numbers $a, b, c, d$, the number $w_n = (an + b)F_n + (cn + d)F_{n-1}$ is an integer for every
natural number $n$ if and only if $d$ is an integer and there are integers $z_1, z_2, z_3$ with
$a = (-z_1 - 3z_2 + 2z_3)/5$, $b = (6z_1 + 3z_2 - 2z_3)/5$ and $c = (-2z_1 + 4z_2 - z_3)/5$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - d$ and
$z_3 = w_3 - d$.

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

/-- **Integer sequences with quadratic Fibonacci coefficients.** Let $F_n$ be the $n$-th Fibonacci
number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every $n \ge 0$. For rational
numbers $a, b, c, d, e, f$, the number
$w_n = (an^2 + bn + c)F_n + (dn^2 + en + f)F_{n-1}$ is an integer for every natural number $n$
if and only if $f$ is an integer and there are integers $z_1, \dots, z_5$ with
$a = (-z_1 + 3z_2 + z_3 - 3z_4 + z_5)/10$,
$b = (-5z_1 - 75z_2 + 15z_3 + 45z_4 - 17z_5)/50$,
$c = (30z_1 + 30z_2 - 10z_3 - 15z_4 + 6z_5)/25$,
$d = (3z_1 - 4z_2 - 3z_3 + 4z_4 - z_5)/10$ and
$e = (-45z_1 + 80z_2 + 15z_3 - 40z_4 + 11z_5)/50$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - f$,
$z_3 = w_3 - f$, $z_4 = w_4 - 2f$ and $z_5 = w_5 - 3f$.

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

/-- **Integer sequences with quadratic and linear Fibonacci coefficients.** Let $F_n$ be the
$n$-th Fibonacci number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every
$n \ge 0$. For rational numbers $a, b, c, d, e$, the number
$w_n = (an^2 + bn + c)F_n + (dn + e)F_{n-1}$ is an integer for every natural number $n$ if and
only if $e$ is an integer and there are integers $z_1, z_2, z_3, z_4$ with
$a = (2z_1 - z_2 - 2z_3 + z_4)/10$, $b = (-56z_1 - 7z_2 + 66z_3 - 23z_4)/50$,
$c = (48z_1 + 6z_2 - 28z_3 + 9z_4)/25$ and $d = (-6z_1 + 18z_2 - 9z_3 + 2z_4)/25$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - e$,
$z_3 = w_3 - e$ and $z_4 = w_4 - 2e$.

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

/-- **Integer sequences with linear Fibonacci coefficients and an alternating term.** Let $F_n$
be the $n$-th Fibonacci number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every
$n \ge 0$. For rational numbers $a, b, c, d, e, f$, the number
$w_n = (an + b)F_n + (cn + d)F_{n-1} + e + f(-1)^n$ is an integer for every natural number $n$
if and only if there are integers $v_0, \dots, v_5$ with
$a = (3v_0 + 2v_1 - 7v_2 - v_3 + 4v_4 - v_5)/5$,
$b = (-3v_0 - 2v_1 - 3v_2 + 6v_3 + 6v_4 - 4v_5)/5$,
$c = (-4v_0 - v_1 + 11v_2 - 2v_3 - 7v_4 + 3v_5)/5$,
$d = -2v_1 + v_2 + 2v_3 - v_4$,
$e = (v_0 + 3v_1 + v_2 - 3v_3 - v_4 + v_5)/2$ and
$f = (v_0 + v_1 - 3v_2 - v_3 + 3v_4 - v_5)/2$.

These integers are then the initial values of the sequence: $v_i = w_i$ for $0 \le i \le 5$.

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
