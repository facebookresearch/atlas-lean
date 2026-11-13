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
is the unique solution of Theorem 2).

Not stated (see the source audit table): Lemma 1,
whose exponents are lost in the extracted statement.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PellLucasDiophantineWanted

/-- **Square Pell–Lucas numbers.** For every natural number $n$, the Pell–Lucas number $Q_n$ is a
perfect square if and only if $n = 0$ or $n = 1$; thus the only square terms of the sequence are
$Q_0 = Q_1 = 1$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 2. -/
theorem_wanted pellLucasSequence_isSquare_iff (n : ℕ) :
    IsSquare (MetaMathlibExt.pellLucasSequence n) ↔
      n = 0 ∨ n = 1

/-- **Pell and Pell–Lucas numbers are coprime.** For every natural number $n$, the Pell number
$P_n$ and the Pell–Lucas number $Q_n$ satisfy $\gcd(P_n, Q_n) = 1$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 3. -/
theorem_wanted gcd_pellNumber_pellLucasSequence (n : ℕ) :
    Nat.gcd (MetaMathlibExt.pellNumber n)
      (MetaMathlibExt.pellLucasSequence n) = 1

/-- **Consecutive Pell–Lucas numbers are coprime.** For every natural number $n$, the Pell–Lucas
numbers $Q_n$ and $Q_{n+1}$ satisfy $\gcd(Q_n, Q_{n+1}) = 1$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 4. -/
theorem_wanted gcd_pellLucasSequence_succ (n : ℕ) :
    Nat.gcd (MetaMathlibExt.pellLucasSequence n)
      (MetaMathlibExt.pellLucasSequence (n + 1)) = 1

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
