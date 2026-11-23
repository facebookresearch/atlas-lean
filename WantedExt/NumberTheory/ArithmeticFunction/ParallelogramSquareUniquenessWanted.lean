/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Parallelogram uniqueness of square numbers for multiplicative functions

Statement from Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for
Multiplicative Functions*, INTEGERS 24 (2024), Article A108. Multiplicative functions are
`ArithmeticFunction ℂ` with `IsMultiplicative`.
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction

/-- **Parallelogram uniqueness of squares for multiplicative functions.** Let $f$ be a
complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$, and suppose $f(4) \ne 0$. Then $f(n) = n^2$ for every natural number $n$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 1 (`integers-2024-A108-thm-1`). -/
public theorem_wanted multiplicative_parallelogram_squares_eq_sq (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (h4 : f 4 ≠ 0) :
    ∀ n : ℕ, f n = (n : ℂ) ^ 2

/-- **Multiplicative parallelogram solutions vanishing at 4.** Let $f$ be a complex-valued
multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$, and suppose $f(4) = 0$. Then one of the following holds:
(1) for every natural number $n$, $f(n) = 0$ if $n \equiv 0 \pmod 4$, $f(n) = 4$ if
$n \equiv 2 \pmod 4$, and $f(n) = 1$ otherwise;
(2) $f(2) = 4$, $f(2^r) = 0$ for every $r \ge 2$, and $f(p^r) = \left(\frac{-1}{p}\right)^r p^r$
for every odd prime $p$ and every $r \ge 1$, where $\left(\frac{-1}{p}\right)$ is the Jacobi
symbol.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 2 (`integers-2024-A108-thm-2`). -/
public theorem_wanted multiplicative_parallelogram_squares_of_f_four_eq_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (h4 : f 4 = 0) :
    (∀ n : ℕ, f n = if n % 4 = 0 then 0 else if n % 4 = 2 then 4 else 1) ∨
      (f 2 = 4 ∧ (∀ r : ℕ, 2 ≤ r → f (2 ^ r) = 0) ∧
        ∀ p r : ℕ, p.Prime → p ≠ 2 → 1 ≤ r →
          f (p ^ r) = ((jacobiSym (-1) p : ℤ) : ℂ) ^ r * (p : ℂ) ^ r)

/-- **Values of a parallelogram-equation multiplicative function at powers of two.** Let $f$ be
a complex-valued multiplicative arithmetic function such that
$f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers $m > n \ge 1$. If $f(4) = 0$,
then $f(2^r) = 0$ for every integer $r \ge 2$. If $f(4) \ne 0$, then $f(2^r) = 2^{2r}$ for every
integer $r \ge 1$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 3 (`integers-2024-A108-thm-3`). -/
public theorem_wanted parallelogram_multiplicative_two_pow (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2)) :
    (f 4 = 0 → ∀ r : ℕ, 2 ≤ r → f (2 ^ r) = 0) ∧
      (f 4 ≠ 0 → ∀ r : ℕ, 1 ≤ r → f (2 ^ r) = (2 : ℂ) ^ (2 * r))

/-- **Parallelogram induction: the value at p² + 1.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p$ is odd and $f(p) = p^2$, then $f(p^2 + 1) = (p^2 + 1)^2$.

The hypothesis $p \ne 2$ is needed: the function with $f(n) = 0$ if $4 \mid n$, $f(n) = 4$ if
$n \equiv 2 \pmod 4$ and $f(n) = 1$ otherwise satisfies the hypotheses for $p = 2$, but
$f(5) = 1$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 1 (`integers-2024-A108-lem-1`). -/
public theorem_wanted parallelogram_multiplicative_sq_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp2 : p ≠ 2) (hfp : f p = (p : ℂ) ^ 2) :
    f (p ^ 2 + 1) = ((p ^ 2 + 1 : ℕ) : ℂ) ^ 2

/-- **Parallelogram induction: the values at p + 2 and (p + 2)².**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p \equiv 3 \pmod 4$, then $f(p + 2) = (p + 2)^2$ and $f((p + 2)^2) = (p + 2)^4$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 2 (`integers-2024-A108-lem-2`). -/
public theorem_wanted parallelogram_multiplicative_add_two (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp4 : p % 4 = 3) :
    f (p + 2) = ((p + 2 : ℕ) : ℂ) ^ 2 ∧ f ((p + 2) ^ 2) = ((p + 2 : ℕ) : ℂ) ^ 4

/-- **Parallelogram induction: the values at k² + 1 and 4k² + 1.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for a natural number $k$, then $f(k^2 + 1) = (k^2 + 1)^2$ and
$f(4k^2 + 1) = (4k^2 + 1)^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 3 (`integers-2024-A108-lem-3`). -/
public theorem_wanted parallelogram_multiplicative_k_sq_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) :
    f (k ^ 2 + 1) = ((k ^ 2 + 1 : ℕ) : ℂ) ^ 2 ∧ f (4 * k ^ 2 + 1) = ((4 * k ^ 2 + 1 : ℕ) : ℂ) ^ 2

/-- **Parallelogram induction: the value at 5k + 3.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for a natural number $k$ with $4 \nmid k$, and $p \ge 19$, then
$f(5k + 3) = (5k + 3)^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 4 (`integers-2024-A108-lem-4`). -/
public theorem_wanted parallelogram_multiplicative_five_k_add_three (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) (hk : ¬ 4 ∣ k) :
    f (5 * k + 3) = ((5 * k + 3 : ℕ) : ℂ) ^ 2

/-- **Parallelogram induction: the value at 6k + 1.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for a natural number $k$ with $k \not\equiv 3 \pmod 4$, and $p \ge 19$,
then $f(6k + 1) = (6k + 1)^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 5 (`integers-2024-A108-lem-5`). -/
public theorem_wanted parallelogram_multiplicative_six_k_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) (hk : k % 4 ≠ 3) :
    f (6 * k + 1) = ((6 * k + 1 : ℕ) : ℂ) ^ 2

/-- **Parallelogram induction: odd prime powers.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p$ is odd and $f(p) = p^2$, then $f(p^r) = p^{2r}$ for every integer $r \ge 2$.

The hypothesis $p \ne 2$ is needed: the function with $f(n) = 0$ if $4 \mid n$, $f(n) = 4$ if
$n \equiv 2 \pmod 4$ and $f(n) = 1$ otherwise satisfies the hypotheses for $p = 2$, but
$f(4) = 0$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 4 (`integers-2024-A108-thm-4`). -/
public theorem_wanted parallelogram_multiplicative_prime_pow (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp2 : p ≠ 2) (hfp : f p = (p : ℂ) ^ 2) :
    ∀ r : ℕ, 2 ≤ r → f (p ^ r) = (p : ℂ) ^ (2 * r)

/-- **Parallelogram induction: primes congruent to 1 mod 4.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p \equiv 1 \pmod 4$, then $f(p) = p^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 5 (`integers-2024-A108-thm-5`). -/
public theorem_wanted parallelogram_multiplicative_prime_one_mod_four (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp4 : p % 4 = 1) :
    f p = (p : ℂ) ^ 2

/-- **Parallelogram induction: primes congruent to 3 mod 4 from 19 on.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for some natural number $k$ and $p \ge 19$, then $f(p) = p^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 6 (`integers-2024-A108-thm-6`). -/
public theorem_wanted parallelogram_multiplicative_prime_three_mod_four (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) :
    f p = (p : ℂ) ^ 2

end

end MetaMathlibExt
