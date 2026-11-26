/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Diophantine equation `Q_n^x + Q_{n+1}^x = y^2`

Statements from Sérgio Mendes, "The Diophantine
Equation `Q_n^x + Q_{n+1}^x = y^2`", *INTEGERS* 26
(2026), Article A72
(<https://math.colgate.edu/~integers/vol26.html>).

The Pell numbers `P_n` and Pell–Lucas numbers `Q_n`
are the existing `MetaMathlibExt.pellNumber`
(`0, 1, 2, 5, …`) and
`MetaMathlibExt.pellLucasSequence` (`1, 1, 3, 7, …`),
matching the paper's normalizations. All statements
were checked numerically on initial ranges (square
terms and gcds for `n < 200`; the two Diophantine
statements on bounded grids, where `(n, x, y) = (1, 1, 2)`
is the unique solution of Theorem 2). The square-terms
statement `pellLucasSequence_isSquare_iff` is now proved
in `MathlibExt.NumberTheory.PellLucasDiophantinePellLucasSequenceIsSquareIff`.
Lemma 1 (quoted
from the paper's reference [6]) is stated over `ℤ` with
its exponents read from the journal PDF and was checked
for `p ∈ {3, 5, 7}`, `|a|, |b| ≤ 60`, `2 ≤ k < 12`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.PellLucasDiophantine
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.PellLucasDiophantinePellLucasSequenceIsSquareIff

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PellLucasDiophantineWanted

/-- **Lemma 1** (quoted from [6]): let `p` be an odd
prime and `a, b, c, k` integers with `gcd(a, b) = 1` and
`k ≥ 2`. If `a^p + b^p = c^k`, then `a + b = d^k` or
`a + b = p^(k-1) d^k` for some integer `d`. The exponent
`k` is a natural number (`k ≥ 2`).

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", *INTEGERS* 26 (2026),
Article A72, Lemma 1. -/
theorem_wanted add_eq_pow_or_eq_prime_pow_mul_pow_of_pow_add_pow_eq_pow
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b c : ℤ}
    (hab : Int.gcd a b = 1) {k : ℕ} (hk : 2 ≤ k)
    (h : a ^ p + b ^ p = c ^ k) :
    ∃ d : ℤ, a + b = d ^ k ∨ a + b = (p : ℤ) ^ (k - 1) * d ^ k

/-- **Pell and Pell–Lucas numbers are coprime.** For every natural number $n$, the Pell number
$P_n$ and the Pell–Lucas number $Q_n$ satisfy $\gcd(P_n, Q_n) = 1$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 3. -/
theorem_wanted gcd_pellNumber_pellLucasSequence (n : ℕ) :
    Nat.gcd (MetaMathlibExt.pellNumber n)
      (MetaMathlibExt.pellLucasSequence n) = 1

/-- **Sums of two coprime positive $n$-th powers are not squares for $n \ge 4$.** Let $n \ge 4$
be a natural number and let $x$ and $y$ be coprime positive integers. Then $x^n + y^n$ is not a
perfect square: there is no natural number $z$ with $x^n + y^n = z^2$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Theorem 1. -/
theorem_wanted pow_add_pow_ne_sq (n x y z : ℕ)
    (hn : 4 ≤ n) (hx : 0 < x) (hy : 0 < y)
    (hxy : Nat.Coprime x y) :
    x ^ n + y ^ n ≠ z ^ 2

/-- **Sums of powers of consecutive Pell–Lucas numbers that are squares.** Let $Q_n$ denote the
Pell–Lucas numbers. For natural numbers $n$, $x$ and $y$, the equation $Q_n^x + Q_{n+1}^x = y^2$
holds if and only if $n = 1$, $x = 1$ and $y = 2$; that is, its only solution in natural numbers
is $Q_1 + Q_2 = 1 + 3 = 2^2$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Theorem 2. -/
theorem_wanted pellLucasSequence_pow_add_pow_eq_sq
    (n x y : ℕ) :
    MetaMathlibExt.pellLucasSequence n ^ x +
        MetaMathlibExt.pellLucasSequence (n + 1) ^ x
        = y ^ 2 ↔
      n = 1 ∧ x = 1 ∧ y = 2

end MathlibExt.NumberTheory.PellLucasDiophantineWanted
