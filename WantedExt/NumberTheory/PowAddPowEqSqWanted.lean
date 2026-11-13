/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the Diophantine equation `n^x + (5p)^y = z^2`

Statements from Suton Tadee, "On the Diophantine
Equation `n^x + (5p)^y = z^2`", *INTEGERS* 24 (2024),
Article A68
(<https://math.colgate.edu/~integers/vol24.html>).

Equation (1) is `n^x + (5p)^y = z^2` in nonnegative
integers, with `p` an odd prime. All solution
classifications and non-existence claims below were
checked by brute-force search over small ranges; the
extraction's flattened `√` set-builders are read as
`z^2 = n + 1` resp. `z^2 = 5p + 1` side conditions.

Not stated (see the source audit table): Theorem 1
(the special case `u^2 - v^q = 1` of Mihăilescu's
theorem, already covered by
`MathlibExt.NumberTheory.MihailescuWanted.mihailescu`)
and Corollary 2 (false as extracted: its equation
must have been flattened).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

/-- **Solutions of $2^x + 1 = z^2$.** For natural numbers $x$ and $z$, $2^x + 1 = z^2$ holds if
and only if $x = 3$ and $z = 3$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 1. -/
theorem_wanted two_pow_add_one_eq_sq (x z : ℕ) :
    2 ^ x + 1 = z ^ 2 ↔ x = 3 ∧ z = 3

/-- **Solutions of $n^x + 1 = z^2$ for $n \ne 2$.** Let $n \ge 1$ be a natural number with
$n \ne 2$. For natural numbers $x$ and $z$, $n^x + 1 = z^2$ holds if and only if $x = 1$ and
$z^2 = n + 1$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 1. -/
theorem_wanted pow_add_one_eq_sq (n x z : ℕ) (hn : 1 ≤ n)
    (hn2 : n ≠ 2) :
    n ^ x + 1 = z ^ 2 ↔ x = 1 ∧ z ^ 2 = n + 1

/-- **The case $x = 0$ of $n^x + (5p)^y = z^2$.** Let $p$ be a prime with $p \ne 2$. For natural
numbers $y$ and $z$, $1 + (5p)^y = z^2$ holds if and only if $y = 1$ and $z^2 = 5p + 1$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 1. -/
theorem_wanted one_add_pow_eq_sq (p y z : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    1 + (5 * p) ^ y = z ^ 2 ↔ y = 1 ∧ z ^ 2 = 5 * p + 1

/-- **Evenness of $x$ in $n^x + (5p)^y = z^2$ when $n \equiv 2, 3 \pmod 5$.** Let $p$ be a prime
and $n$ a natural number with $n \equiv 2 \pmod 5$ or $n \equiv 3 \pmod 5$. If natural numbers
$x$, $y$, $z$ with $y > 0$ satisfy $n^x + (5p)^y = z^2$, then $x$ is even.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 2. -/
theorem_wanted even_of_pos_exp (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 5 = 2 ∨ n % 5 = 3) (hy : 0 < y)
    (h : n ^ x + (5 * p) ^ y = z ^ 2) :
    Even x

/-- **Opposite parity of the exponents in $n^x + (5p)^y = z^2$ when $n \equiv p \equiv 3 \pmod 4$.**
Let $p$ be a prime and $n$ a natural number with $n \equiv 3 \pmod 4$ and $p \equiv 3 \pmod 4$.
If natural numbers $x$, $y$, $z$ satisfy $n^x + (5p)^y = z^2$, then $x$ and $y$ have opposite
parity.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 3. -/
theorem_wanted opposite_parity (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 4 = 3) (hp4 : p % 4 = 3)
    (h : n ^ x + (5 * p) ^ y = z ^ 2) :
    x % 2 ≠ y % 2

/-- **No solutions of $n^x + (5p)^y = z^2$ when $n \equiv p \equiv 1 \pmod 4$.** Let $p$ be a
prime and $n$ a natural number with $n \equiv 1 \pmod 4$ and $p \equiv 1 \pmod 4$. Then there
are no natural numbers $x$, $y$, $z$ with $n^x + (5p)^y = z^2$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 2. -/
theorem_wanted no_solution_mod_four_one (n p : ℕ) (hp : p.Prime)
    (hn : n % 4 = 1) (hp4 : p % 4 = 1) :
    ¬ ∃ x y z : ℕ, n ^ x + (5 * p) ^ y = z ^ 2

/-- **Solutions of $2^x + (5p)^y = z^2$ for $p \equiv 3 \pmod 4$.** Let $p$ be a prime with
$p \equiv 3 \pmod 4$. For natural numbers $x$, $y$, $z$, $2^x + (5p)^y = z^2$ holds if and
only if $(x, y, z) = (3, 0, 3)$, or $p = 3$ and $(x, y, z) = (6, 2, 17)$, or $x = 0$, $y = 1$
and $z^2 = 5p + 1$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 3. -/
theorem_wanted two_pow_solutions (p x y z : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) :
    2 ^ x + (5 * p) ^ y = z ^ 2 ↔
      (x = 3 ∧ y = 0 ∧ z = 3) ∨
        (p = 3 ∧ x = 6 ∧ y = 2 ∧ z = 17) ∨
        (x = 0 ∧ y = 1 ∧ z ^ 2 = 5 * p + 1)

/-- **Solutions of $n^x + (5p)^y = z^2$ for $n \equiv 3, 27 \pmod{60}$ and $p \equiv 7 \pmod{12}$.**
Let $p$ be a prime with $p \equiv 7 \pmod{12}$, and let $n$ be a natural number with
$n \equiv 3 \pmod{60}$ or $n \equiv 27 \pmod{60}$ such that $\gcd(n, p) = 1$ and
$\gcd(n, 5p - 1) = 1$. For natural numbers $x$, $y$, $z$, $n^x + (5p)^y = z^2$ holds if and
only if either $x = 0$, $y = 1$ and $z^2 = 5p + 1$, or $x = 1$, $y = 0$ and $z^2 = n + 1$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 4. -/
theorem_wanted solutions_mod_sixty (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 60 = 3 ∨ n % 60 = 27) (hp12 : p % 12 = 7)
    (h1 : Nat.Coprime n p) (h2 : Nat.Coprime n (5 * p - 1)) :
    n ^ x + (5 * p) ^ y = z ^ 2 ↔
      (x = 0 ∧ y = 1 ∧ z ^ 2 = 5 * p + 1) ∨
        (x = 1 ∧ y = 0 ∧ z ^ 2 = n + 1)

/-- **Solutions of $2^x + 15^y = z^2$.** The natural numbers $x$, $y$, $z$ with
$2^x + 15^y = z^2$ are exactly $(x, y, z) = (3, 0, 3)$, $(0, 1, 4)$ and $(6, 2, 17)$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 3. -/
theorem_wanted two_pow_add_fifteen_pow (x y z : ℕ) :
    2 ^ x + 15 ^ y = z ^ 2 ↔
      (x = 3 ∧ y = 0 ∧ z = 3) ∨ (x = 0 ∧ y = 1 ∧ z = 4) ∨
        (x = 6 ∧ y = 2 ∧ z = 17)

/-- **Solutions of $3^x + 35^y = z^2$.** The natural numbers $x$, $y$, $z$ with
$3^x + 35^y = z^2$ are exactly $(x, y, z) = (1, 0, 2)$ and $(x, y, z) = (0, 1, 6)$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 4. -/
theorem_wanted three_pow_add_thirtyfive_pow (x y z : ℕ) :
    3 ^ x + 35 ^ y = z ^ 2 ↔
      (x = 1 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 1 ∧ z = 6)

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
