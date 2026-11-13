/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PracticalNumber
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.ModEq

/-!
# Sums of practical numbers and polygonal numbers

Statements from Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and
Polygonal Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1
(arXiv:2403.13533). In the paper "natural number" means positive integer; practical numbers
are `MetaMathlibExt.IsPracticalNumber`. The paper's `s`-gonal number `P_s(n)` is the canonical
`Nat.polygonalNumber s n`; triangular numbers are `Nat.polygonalNumber 3 k = k (k + 1) / 2`
with `k ≥ 0` (the paper's Lemma 5, arXiv Lemma 3.3, counts `0`).
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction
open scoped Nat

/-- **Every positive integer is a practical number plus a triangular number.** For every natural
number $n > 0$ there are a practical number $q$ and a natural number $k$ with
$n = q + k(k+1)/2$; the case $k = 0$, where the triangular number is $0$, is allowed.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 1
(`jis-2024-24.5.1-thm-1`). -/
public theorem_wanted exists_practical_add_triangular (n : ℕ) (hn : 0 < n) :
    ∃ q k : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber 3 k

/-- **Large integers as a practical number plus two polygonal numbers.** Let $s > 3$ be a natural
number and, for a natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th
$s$-gonal number, so that $P_s(0) = 0$. There is a natural number $N$ such that every natural
number $n > N$ can be written as $n = q + P_s(x) + P_s(y)$ with $q$ a practical number and
$x, y$ natural numbers.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 2
(`jis-2024-24.5.1-thm-2`). -/
public theorem_wanted eventually_practical_add_two_polygonal (s : ℕ) (hs : 3 < s) :
    ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
      IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s x + Nat.polygonalNumber s y

/-- **Square roots modulo powers of two.** For all natural numbers $m > 0$ and $n > 0$ there is
a natural number $x$ with $1 \le x \le 2^m - 1$ and $x^2 \equiv 8n + 1 \pmod{2^{m+2}}$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 3
(arXiv Lemma 3.1; `jis-2024-24.5.1-lem-3`). -/
public theorem_wanted exists_sq_modEq_eight_mul_add_one (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ 2 ^ m - 1 ∧ x ^ 2 ≡ 8 * n + 1 [MOD 2 ^ (m + 2)]

/-- **Products of a practical number with small factors.** Let $m$ be a practical number and let
$\sigma(m)$ denote the sum of the positive divisors of $m$. Then for every natural number $n$
with $1 \le n \le \sigma(m) + 1$, the product $mn$ is a practical number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 4
(arXiv Lemma 3.2; `jis-2024-24.5.1-lem-4`), quoting Margenstern. -/
public theorem_wanted isPracticalNumber_mul_of_le_sigma_add_one (m n : ℕ)
    (hm : IsPracticalNumber m) (hn : 0 < n) (hnm : n ≤ sigma 1 m + 1) :
    IsPracticalNumber (m * n)

/-- **Odd squares and triangular numbers.** For every odd natural number $x$, the number
$(x^2 - 1)/8$ is a triangular number: there is a natural number $k$ with
$(x^2 - 1)/8 = p_3(k)$, where $p_3(k) = k(k+1)/2$ is the $k$-th $3$-gonal number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 5
(arXiv Lemma 3.3; `jis-2024-24.5.1-lem-5`). -/
public theorem_wanted sq_sub_one_div_eight_eq_triangular (x : ℕ) (hx : Odd x) :
    ∃ k : ℕ, (x ^ 2 - 1) / 8 = Nat.polygonalNumber 3 k

/-- **Sums of two polygonal numbers modulo an odd prime.** For a natural number $s > 3$ and a
natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. For
every odd prime $p$ and every natural number $n > 0$ there are natural numbers $x, y > 0$ with
$P_s(x) + P_s(y) \equiv n \pmod{p}$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 6
(arXiv Lemma 4.1; `jis-2024-24.5.1-lem-6`). -/
public theorem_wanted exists_polygonal_add_polygonal_modEq_prime (p n s : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 0 < n) (hs : 3 < s) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p]

/-- **Parity of sums of two polygonal numbers.** For a natural number $s > 3$ and a natural
number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. For every
natural number $n > 0$ there are natural numbers $x, y > 0$ such that
$P_s(x_1) + P_s(y_1) \equiv n \pmod{2}$ for all natural numbers $x_1, y_1 > 0$ with
$x_1 \equiv x \pmod{4}$ and $y_1 \equiv y \pmod{4}$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 7
(arXiv Lemma 4.2; `jis-2024-24.5.1-lem-7`). -/
public theorem_wanted exists_polygonal_add_polygonal_modEq_two (n s : ℕ) (hn : 0 < n)
    (hs : 3 < s) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ ∀ x₁ y₁ : ℕ, 0 < x₁ → 0 < y₁ → x₁ ≡ x [MOD 4] → y₁ ≡ y [MOD 4] →
      Nat.polygonalNumber s x₁ + Nat.polygonalNumber s y₁ ≡ n [MOD 2]

/-- **Sums of two squares modulo prime powers.** Let $p$ be a prime with $p \equiv 1 \pmod{4}$.
For all natural numbers $n > 0$ and $k > 0$ there are natural numbers $x, y > 0$ with
$x^2 + y^2 \equiv n \pmod{p^k}$ and $p \nmid y$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 8
(arXiv Lemma 4.3; `jis-2024-24.5.1-lem-8`). -/
public theorem_wanted exists_sq_add_sq_modEq_prime_pow (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hn : 0 < n) (hk : 0 < k) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 ≡ n [MOD p ^ k] ∧ ¬ p ∣ y

/-- **Sums of two polygonal numbers modulo prime powers.** For a natural number $s > 3$ and a
natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. There
is a prime $p$ with $p \equiv 1 \pmod{4}$ and $p \nmid s - 2$ such that for all natural numbers
$k > 0$ and $n > 0$ there are natural numbers $x, y > 0$ with
$P_s(x) + P_s(y) \equiv n \pmod{p^k}$.

The paper's statement asks only for an odd prime; the condition $p \equiv 1 \pmod{4}$ is the
choice made in its proof via Lemma 8 (arXiv Lemma 4.3).

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 9
(arXiv Lemma 4.4; `jis-2024-24.5.1-lem-9`). -/
public theorem_wanted exists_prime_polygonal_add_polygonal_modEq_prime_pow (s : ℕ)
    (hs : 3 < s) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ ¬ p ∣ s - 2 ∧ ∀ k n : ℕ, 0 < k → 0 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p ^ k]

/-- **Quadratic upper bound for polygonal numbers.** For a natural number $s > 3$ and a natural
number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. For every natural
number $c$ there is a natural number $A$ such that $2 P_s(2cx) \le A x^2$ for every natural
number $x \ge 1$.

The paper states this only for one specific prime $c$, the prime chosen in Lemma 9 (arXiv
Lemma 4.4), and for real $x$; here $c$ is an arbitrary natural number and $x$ is a natural number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 10
(arXiv Lemma 4.5; `jis-2024-24.5.1-lem-10`). -/
public theorem_wanted exists_two_polygonal_two_mul_le_mul_sq (s c : ℕ) (hs : 3 < s) :
    ∃ A : ℕ, ∀ x : ℕ, 1 ≤ x → 2 * Nat.polygonalNumber s (2 * c * x) ≤ A * x ^ 2

/-- **Practical numbers divisible by neither 3 nor 4.** If $q$ is a practical number that is
divisible by neither $3$ nor $4$, then $q = 1$ or $q = 2$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 11
(arXiv Lemma 4.6; `jis-2024-24.5.1-lem-11`). -/
public theorem_wanted isPracticalNumber_eq_one_or_two (q : ℕ) (hq : IsPracticalNumber q)
    (h3 : ¬ 3 ∣ q) (h4 : ¬ 4 ∣ q) :
    q = 1 ∨ q = 2

/-- **Exceptions to sums of a practical number and polygonal numbers.** (a) Let $s \ge 3$ with
$s \equiv 0$ or $s \equiv 4 \pmod{12}$. Then there are infinitely many positive integers $n$ that
cannot be written as $n = q + p_s(m)$ with $q$ a practical number and $m \ge 0$ an integer, where
$p_s(m)$ is the $m$-th $s$-gonal number. (b) For every natural number $M$ there is a natural
number $S$ such that for every $t \ge S$ there are at least $M$ positive integers $n$ that cannot
be written as $n = q + p_t(x) + p_t(y)$ with $q$ a practical number and integers $x, y \ge 0$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Proposition 12
(arXiv Proposition 4.7; `jis-2024-24.5.1-prop-12`). -/
public theorem_wanted practical_add_polygonal_exceptions (s : ℕ) :
    ((3 ≤ s ∧ (s % 12 = 0 ∨ s % 12 = 4)) →
      {n : ℕ | 0 < n ∧
        ¬ ∃ q m : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s m}.Infinite) ∧
    ∀ M : ℕ, ∃ S : ℕ, ∀ t ≥ S, ∃ F : Finset ℕ, M ≤ F.card ∧ ∀ n ∈ F, 0 < n ∧
      ¬ ∃ q x y : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber t x + Nat.polygonalNumber t y

end

end MetaMathlibExt
