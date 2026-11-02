/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quotients of a more general theorem of Wilson

Statements from Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", *INTEGERS* 25 (2025), Article A93
(<https://math.colgate.edu/~integers/z93/z93.pdf>).

Non-composite means `1` or prime.  Congruences for the rational
numbers `Z` and `Z+` are stated through the integer values whose
existence is asserted in the corresponding integrality theorems;
Theorem 6 is stated in the usual rational form that the numerator
of the difference is divisible by `p`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

/-- **Morozov's Wilson quotients.** For natural numbers $k$ and $n$, $M_k(n)$ is the rational
number

$$M_k(n) = \frac{1 + (-1)^k \, k! \, (n - k - 1)!}{n},$$

where $n - k - 1$ is truncated subtraction of natural numbers and division by $0$ gives $0$. -/
def wilsonQuotientM (k n : ℕ) : ℚ :=
  (1 + (-1 : ℚ) ^ k * (Nat.factorial k * Nat.factorial (n - k - 1) : ℚ)) / n

/-- **Morozov's sign-adjusted Wilson quotients.** For natural numbers $k$ and $n$, $M_k^+(n)$ is
the rational number

$$M_k^+(n) = \frac{(-1)^k + k! \, (n - k - 1)!}{n},$$

where $n - k - 1$ is truncated subtraction of natural numbers and division by $0$ gives $0$. -/
def wilsonQuotientMPlus (k n : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k + (Nat.factorial k * Nat.factorial (n - k - 1) : ℚ)) / n

/-- **Morozov's Wilson quotient sum.** For a natural number $n$, $Z(n)$ is the rational number
$Z(n) = \sum_{k=0}^{n-1} M_k(n)$, where $M_k(n)$ are Morozov's Wilson quotients. -/
def wilsonQuotientZ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, wilsonQuotientM k n

/-- **Morozov's sign-adjusted Wilson quotient sum.** For a natural number $n$, $Z^+(n)$ is the
rational number $\sum_{k=0}^{n-1} M_k^+(n)$, where $M_k^+(n) = ((-1)^k + k!\,(n-k-1)!)/n$ is
Morozov's sign-adjusted quotient. -/
def wilsonQuotientZPlus (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, wilsonQuotientMPlus k n

/-- **A generalized Wilson criterion for primality.** Let $n \ge 1$ and $k < n$ be natural
numbers. Then $(-1)^k \, k! \, (n - k - 1)! \equiv -1 \pmod{n}$ if and only if $n = 1$ or $n$
is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Corollary 1. -/
theorem_wanted neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff
    (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) :
    ((-1 : ℤ) ^ k * (Nat.factorial k * Nat.factorial (n - k - 1) : ℤ) ≡
        -1 [ZMOD (n : ℤ)]) ↔
      n = 1 ∨ n.Prime

/-- **The Wilson quotient sum is an integer.** For every natural number $n \ge 1$, Morozov's
Wilson quotient sum $Z(n)$ is an integer.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 1. -/
theorem_wanted exists_int_eq_wilsonQuotientZ
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ n

/-- **When the sign-adjusted Wilson quotient sum is a natural number.** For every natural number
$n \ge 1$, Morozov's sign-adjusted Wilson quotient sum $Z^+(n)$ is a natural number if and only
if $n$ is even, $n = 1$, or $n$ is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 2. -/
theorem_wanted exists_nat_eq_wilsonQuotientZPlus_iff
    (n : ℕ) (hn : 1 ≤ n) :
    (∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus n) ↔
      n % 2 = 0 ∨ n = 1 ∨ n.Prime

/-- **The Wilson quotient sum Z(n) modulo n.** Let $n \ge 1$ be a natural number. Morozov's
Wilson quotient sum $Z(n)$ is an integer; moreover $Z(n) \equiv 1 \pmod{n}$ if $n$ is neither
$1$ nor prime, and $Z(n) \equiv -1 \pmod{n}$ if $n = 1$ or $n$ is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 3. -/
theorem_wanted exists_int_eq_wilsonQuotientZ_and_modEq
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ n ∧
      ((¬(n = 1 ∨ n.Prime) → z ≡ 1 [ZMOD (n : ℤ)]) ∧
        ((n = 1 ∨ n.Prime) → z ≡ -1 [ZMOD (n : ℤ)]))

/-- **A primality criterion from the Wilson quotient sum Z(2n − 1).** For every natural number
$n \ge 1$, Morozov's Wilson quotient sum $Z(2n - 1)$ is an integer, and it is divisible by $n$
if and only if $n = 1$ or $n$ is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 4. -/
theorem_wanted exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ (2 * n - 1) ∧
      ((z ≡ 0 [ZMOD (n : ℤ)]) ↔ n = 1 ∨ n.Prime)

/-- **The sign-adjusted Wilson quotient sum Z⁺(2n) modulo 2n.** Let $n \ge 1$ be a natural
number. Morozov's sign-adjusted Wilson quotient sum $Z^+(2n)$ is an integer; it satisfies
$Z^+(2n) \equiv 0 \pmod{2n}$ if $n = 2$ or $n$ is neither $1$ nor prime, and
$Z^+(2n) \equiv n + 1 \pmod{2n}$ if $n$ is an odd prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 5, equations (8) and (9). -/
theorem_wanted exists_int_eq_wilsonQuotientZPlus_two_mul_and_modEq
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZPlus (2 * n) ∧
      (((n = 2 ∨ ¬(n = 1 ∨ n.Prime)) → z ≡ 0 [ZMOD (2 * n : ℤ)]) ∧
        (((n.Prime ∧ n ≠ 2) → z ≡ (n : ℤ) + 1 [ZMOD (2 * n : ℤ)])))

/-- **A Bernoulli–harmonic congruence for the sign-adjusted Wilson quotient sum.** Let $p$ be an
odd prime, let $B_m$ denote the Bernoulli numbers, and let $H_k = \sum_{j=1}^{k} 1/j$ denote the
harmonic numbers, with $H_0 = 0$. Then $p$ divides the numerator, in lowest terms, of the
rational number

$$Z^+(p) - \Bigl(B_{2(p-1)} - B_{p-1} - \sum_{k=0}^{p-1} (-1)^k H_k\Bigr),$$

where $Z^+(p)$ is Morozov's sign-adjusted Wilson quotient sum.

This is the congruence obtained by summing the paper's Equation (7). The printed simplification
of the alternating harmonic sum to $H_{p-1}/2$ is false already at $p = 3$.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 6 and Equation (7). -/
theorem_wanted prime_dvd_num_wilsonQuotientZPlus_sub_bernoulli_alternating
    (p : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1) :
    (p : ℤ) ∣ (wilsonQuotientZPlus p -
      (bernoulli (2 * (p - 1)) - bernoulli (p - 1) -
        ∑ k ∈ Finset.range p, (-1 : ℚ) ^ k * harmonic k)).num

end MathlibExt.NumberTheory.WilsonQuotientsWanted
