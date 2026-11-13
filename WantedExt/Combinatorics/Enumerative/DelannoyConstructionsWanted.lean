/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Delannoy constructions

Statements from Steven Edwards and William Griffiths, "Delannoy
Constructions", *Journal of Integer Sequences* 27 (2024), Article 24.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Edwards/ed6.html>).

The Delannoy number `D(m, n)` is taken from the existing Delannoy triangle
`MetaMathlibExt.ordinaryRiordanPascalLikeMatrix (m + n) m 1
= ∑_j C(m, j) C(m + n - j, m)`.

The generalized Delannoy numbers `D^k(m, n)` and `D_k(m, n)` are the paper's binomial sums
(`genDelannoyUpper`, `genDelannoyLower`); a Delannoy array is any `R : ℕ → ℕ → ℤ` satisfying the
Delannoy recurrence, and `R^i` is its `i`-fold horizontal sum. The lattice-path interpretations
(Theorems 1 and 2) are not stated.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix

set_option autoImplicit false

namespace MetaMathlibExt

namespace DelannoyConstructions

@[expose] public section

open Finset

/-- **Delannoy numbers as a sum of powers of two.** For all natural numbers $m$ and $n$, the
Delannoy number $D(m, n)$, that is, the Delannoy triangle entry $T(m + n, m; 1)$, satisfies
$D(m, n) = \sum_{j=0}^{\min(m, n)} \binom{m}{j} \binom{n}{j} 2^j$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 8
(`jis-2024-24.1.8-thm-8`). -/
public theorem_wanted delannoy_eq_sum_choose_mul_choose_two_pow (m n : ℕ) :
    ordinaryRiordanPascalLikeMatrix (m + n) m 1 =
      ∑ j ∈ range (min m n + 1), (m.choose j : ℤ) * (n.choose j : ℤ) * 2 ^ j

/-- **Parity of a sum of adjacent binomial coefficients.** For all natural numbers $n$ and $k$
with $k \ge 1$, $\binom{n}{k} + \binom{n+1}{k} \equiv \binom{n}{k-1} \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Lemma 15
(`jis-2024-24.1.8-lem-15`). -/
public theorem_wanted choose_add_choose_succ_modEq_two (n k : ℕ) (hk : 1 ≤ k) :
    n.choose k + (n + 1).choose k ≡ n.choose (k - 1) [MOD 2]

/-- **Generalized Delannoy number with upper index.** For natural numbers $k$, $m$ and $n$, the
generalized Delannoy number $D^k(m, n)$ is the natural number

$$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}.$$

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1 (definition of `D^k(m, n)`). -/
public def genDelannoyUpper (k m n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), (m + n + k - j).choose (n + k) * n.choose j

/-- **Lower generalized Delannoy number.** For natural numbers $k$, $m$ and $n$, the generalized
Delannoy number $D_k(m, n)$ is
$$D_k(m, n) = \sum_{j=0}^{n} \binom{m + n - k - j}{n - k} \binom{n}{j},$$
where each subtraction is truncated at $0$. The definition is intended for $m, n \ge k$, where
no truncation occurs.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1 (definition of `D_k(m, n)`). -/
public def genDelannoyLower (k m n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), (m + n - k - j).choose (n - k) * n.choose j

/-- **An upper generalized Delannoy number equal to $13$.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. Then $D^0(2, 2) = 13$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Table 1. -/
public theorem genDelannoyUpper_zero_two_two : genDelannoyUpper 0 2 2 = 13 := by decide

/-- **An upper generalized Delannoy number equal to $44$.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. Then $D^1(3, 2) = 44$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Table 1. -/
public theorem genDelannoyUpper_one_three_two : genDelannoyUpper 1 3 2 = 44 := by decide

/-- **A value of the lower generalized Delannoy number.** The lower generalized Delannoy number
$D_1(2, 2)$ equals $8$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1 (central theorem `D_k(m, n) = 2^k D^k(n - k, m - k)`). -/
public theorem genDelannoyLower_one_two_two : genDelannoyLower 1 2 2 = 8 := by decide

/-- **The lower and upper generalized Delannoy numbers agree at index zero.** For natural
numbers $k$, $m$ and $n$, let
$D_k(m, n) = \sum_{j=0}^{n} \binom{m + n - k - j}{n - k} \binom{n}{j}$ (with subtraction
truncated at $0$) and
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ be the lower
and upper generalized Delannoy numbers. Then $D_0(m, n) = D^0(m, n)$ for all natural numbers
$m$ and $n$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Section 1. -/
public theorem genDelannoyLower_zero (m n : ℕ) : genDelannoyLower 0 m n = genDelannoyUpper 0 m n := by
  simp [genDelannoyLower, genDelannoyUpper]

/-- **Horizontal sum identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$,
$D^k(m, n) + D^k(m, n + 1) = 2 D^{k+1}(m, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 3
(`jis-2024-24.1.8-thm-3`). -/
public theorem_wanted genDelannoyUpper_add_succ_right (k m n : ℕ) :
    genDelannoyUpper k m n + genDelannoyUpper k m (n + 1) = 2 * genDelannoyUpper (k + 1) m n

/-- **Vertical sum identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $k \ge 1$,
$D^k(m, n) + D^k(m + 1, n) = D^{k-1}(m + 1, n + 1)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 4
(`jis-2024-24.1.8-thm-4`). -/
public theorem_wanted genDelannoyUpper_add_succ_left (k m n : ℕ) (hk : 1 ≤ k) :
    genDelannoyUpper k m n + genDelannoyUpper k (m + 1) n = genDelannoyUpper (k - 1) (m + 1) (n + 1)

/-- **Horizontal difference identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $m \ge 1$,
$D^k(m, n + 1) - D^k(m, n) = 2 D^{k+1}(m - 1, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 5
(`jis-2024-24.1.8-cor-5`). -/
public theorem_wanted genDelannoyUpper_succ_right_sub (k m n : ℕ) (hm : 1 ≤ m) :
    (genDelannoyUpper k m (n + 1) : ℤ) - genDelannoyUpper k m n =
      2 * genDelannoyUpper (k + 1) (m - 1) n

/-- **Vertical difference identity for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$ with $k \ge 1$,
$D^k(m + 1, n) - D^k(m, n) = D^{k-1}(m + 1, n)$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 6
(`jis-2024-24.1.8-cor-6`). -/
public theorem_wanted genDelannoyUpper_succ_left_sub (k m n : ℕ) (hk : 1 ≤ k) :
    (genDelannoyUpper k (m + 1) n : ℤ) - genDelannoyUpper k m n = genDelannoyUpper (k - 1) (m + 1) n

/-- The four relationship identities for `D_k` (`k ≥ 1`, `m, n ≥ k`):
`D_k(m, n) + D_k(m, n + 1) = 2 D_(k-1)(m, n)`, `D_k(m, n) + D_k(m + 1, n) = D_(k+1)(m + 1, n + 1)`,
`D_k(m, n + 1) - D_k(m, n) = 2 D_(k-1)(m - 1, n)`, `D_k(m + 1, n) - D_k(m, n) = D_(k+1)(m + 1, n)`.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 7
(`jis-2024-24.1.8-thm-7`). -/
public theorem_wanted genDelannoyLower_relations (k m n : ℕ) (hk : 1 ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    genDelannoyLower k m n + genDelannoyLower k m (n + 1) = 2 * genDelannoyLower (k - 1) m n ∧
      genDelannoyLower k m n + genDelannoyLower k (m + 1) n =
        genDelannoyLower (k + 1) (m + 1) (n + 1) ∧
      (genDelannoyLower k m (n + 1) : ℤ) - genDelannoyLower k m n =
        2 * genDelannoyLower (k - 1) (m - 1) n ∧
      (genDelannoyLower k (m + 1) n : ℤ) - genDelannoyLower k m n = genDelannoyLower (k + 1) (m + 1) n

/-- **Lower generalized Delannoy numbers as a sum of powers of two.** For natural numbers $k$, $m$,
$n$ with $m \ge k$ and $n \ge k$, the lower generalized Delannoy number $D_k(m, n)$ satisfies
$D_k(m, n) = \sum_{j=0}^{\min(m-k, n-k)} \binom{m-k}{j} \binom{n}{j+k} 2^{j+k}$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 9
(`jis-2024-24.1.8-thm-9`). -/
public theorem_wanted genDelannoyLower_eq_sum_two_pow (k m n : ℕ) (hm : k ≤ m) (hn : k ≤ n) :
    genDelannoyLower k m n =
      ∑ j ∈ range (min (m - k) (n - k) + 1), (m - k).choose j * n.choose (j + k) * 2 ^ (j + k)

/-- **Powers-of-two formula for the upper generalized Delannoy numbers.**
For natural numbers $k$, $m$ and $n$, write
$D^k(m, n) = \sum_{j=0}^{n} \binom{m + n + k - j}{n + k} \binom{n}{j}$ for the upper
generalized Delannoy numbers. For all natural numbers $k$, $m$ and $n$,
$$D^k(m, n) = \sum_{j=0}^{\min(m, n)} \binom{m + k}{j + k} \binom{n}{j} 2^j.$$

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 10
(`jis-2024-24.1.8-thm-10`). -/
public theorem_wanted genDelannoyUpper_eq_sum_two_pow (k m n : ℕ) :
    genDelannoyUpper k m n = ∑ j ∈ range (min m n + 1), (m + k).choose (j + k) * n.choose j * 2 ^ j

/-- **Unified power-of-two sums for generalized Delannoy numbers.** For natural numbers $k$, $m$,
$n$, write $D_k(m, n)$ and $D^k(m, n)$ for the lower and upper generalized Delannoy numbers. If
$m \ge k$ and $n \ge k$, then
$D_k(m, n) = \sum_{j=k}^{\min(m, n)} \binom{m-k}{j-k} \binom{n}{j} 2^j$; and, for all $k$, $m$, $n$,
$D^k(m, n) = \sum_{j=0}^{\min(m, n)} \binom{m+k}{j+k} \binom{n}{j} 2^j$.

With the convention $D_{-k} = D^k$, the second formula is the first with $k$ replaced by $-k$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 11
(`jis-2024-24.1.8-thm-11`). -/
public theorem_wanted genDelannoy_eq_sum_two_pow_unified (k m n : ℕ) :
    (k ≤ m → k ≤ n → genDelannoyLower k m n =
        ∑ j ∈ Ico k (min m n + 1), (m - k).choose (j - k) * n.choose j * 2 ^ j) ∧
      genDelannoyUpper k m n = ∑ j ∈ range (min m n + 1), (m + k).choose (j + k) * n.choose j * 2 ^ j

/-- **Parity of adjacent rows of a Delannoy array.** Let $R(m, n)$, for $m, n \in \mathbb{N}$, be
integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all $m, n$, and let
$m \in \mathbb{N}$. If $R(m, 0) \equiv R(m+1, 0) \pmod 2$, then $R(m, i) \equiv R(m+1, i) \pmod 2$
for all $i$; if $R(m, 0) \not\equiv R(m+1, 0) \pmod 2$, then
$R(m, i) \not\equiv R(m+1, i) \pmod 2$ for all $i$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 13
(`jis-2024-24.1.8-thm-13`). -/
public theorem_wanted delannoyArray_rows_parity (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (m : ℕ) :
    (R m 0 ≡ R (m + 1) 0 [ZMOD 2] → ∀ i, R m i ≡ R (m + 1) i [ZMOD 2]) ∧
      (¬ R m 0 ≡ R (m + 1) 0 [ZMOD 2] → ∀ i, ¬ R m i ≡ R (m + 1) i [ZMOD 2])

/-- **Rows of iterated horizontal sums of a Delannoy array agree mod 2.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for the
$i$-fold horizontal sum. Then for every $i \ge 1$ and all $m, m', n \in \mathbb{N}$,
$R^i(m, n) \equiv R^i(m', n) \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Corollary 14
(`jis-2024-24.1.8-cor-14`). -/
public theorem_wanted delannoyArray_horizontalSum_rows_modEq (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (i : ℕ) (hi : 1 ≤ i)
    (m m' n : ℕ) :
    (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[i] R m n ≡
      (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[i] R m' n [ZMOD 2]

/-- **Parity of iterated horizontal sums of a Delannoy array with binomial seeds.** Let $R(m, n)$,
for $m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for
all $m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for
the $i$-fold horizontal sum, so $R^0 = R$. Let $k \in \mathbb{N}$ and suppose
$R(0, n) = \binom{k+n}{k}$ for all $n$; the values $R(m, 0)$ for $m \ge 1$ are arbitrary. Then
every entry of $R^{k+1}$ is even, and for every $j \le k$ some entry of $R^j$ is odd.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Lemma 16
(`jis-2024-24.1.8-lem-16`). -/
public theorem_wanted delannoyArray_binomial_seeds_parity (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k : ℕ)
    (hseed : ∀ n, R 0 n = (k + n).choose k) :
    (∀ m n, (2 : ℤ) ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[k + 1] R m n) ∧
      ∀ j ≤ k, ∃ m n, ¬ (2 : ℤ) ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[j] R m n

/-- **First horizontal sums of a Delannoy array with binomial seeds.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. Let $k \ge 1$ and suppose $R(0, n) = \binom{k+n}{k}$ for all $n$. Then for all $m$ and
$n$, $R(m, n) + R(m, n+1) \equiv \binom{k+n}{k-1} \pmod 2$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 17
(`jis-2024-24.1.8-thm-17`). -/
public theorem_wanted delannoyArray_binomial_seeds_horizontalSum_modEq (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k : ℕ) (hk : 1 ≤ k)
    (hseed : ∀ n, R 0 n = (k + n).choose k) (m n : ℕ) :
    R m n + R m (n + 1) ≡ (k + n).choose (k - 1) [ZMOD 2]

/-- **Powers of two dividing iterated horizontal sums of a Delannoy array.** Let $R(m, n)$, for
$m, n \in \mathbb{N}$, be integers with $R(m+1, n+1) = R(m, n+1) + R(m+1, n) + R(m, n)$ for all
$m, n$. For an array $S$ let $(HS)(m, n) = S(m, n) + S(m, n+1)$, and write $R^i = H^i R$ for the
$i$-fold horizontal sum. Let $k, i \in \mathbb{N}$ with $i \ge 1$, and suppose
$R(0, n) = \binom{k+n}{k}$ for all $n$. Then every entry of $R^{k+i}$ is divisible by $2^i$, and
some entry of $R^{k+i}$ is not divisible by $2^{i+1}$.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 18
(`jis-2024-24.1.8-thm-18`). -/
public theorem_wanted delannoyArray_binomial_seeds_two_pow_dvd (R : ℕ → ℕ → ℤ)
    (hR : ∀ m n, R (m + 1) (n + 1) = R m (n + 1) + R (m + 1) n + R m n) (k i : ℕ) (hi : 1 ≤ i)
    (hseed : ∀ n, R 0 n = (k + n).choose k) :
    (∀ m n, (2 : ℤ) ^ i ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[k + i] R m n) ∧
      ∃ m n, ¬ (2 : ℤ) ^ (i + 1) ∣ (fun S : ℕ → ℕ → ℤ => fun a b => S a b + S a (b + 1))^[k + i] R m n

end

end DelannoyConstructions

end MetaMathlibExt
