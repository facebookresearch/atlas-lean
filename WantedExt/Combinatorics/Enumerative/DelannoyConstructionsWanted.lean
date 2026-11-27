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
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.DelannoyConstructions
public import MathlibExt.Combinatorics.Enumerative.DelannoyRowsParity
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix

set_option autoImplicit false

namespace MetaMathlibExt

namespace DelannoyConstructions

@[expose] public section

open Finset

/-- The four relationship identities for `D_k` (`k ≥ 1`, `m, n ≥ k`):
`D_k(m, n) + D_k(m, n + 1) = 2 D_(k-1)(m, n)`, `D_k(m, n) + D_k(m + 1, n) = D_(k+1)(m + 1, n + 1)`,
`D_k(m, n + 1) - D_k(m, n) = 2 D_(k-1)(m - 1, n)`, `D_k(m + 1, n) - D_k(m, n) = D_(k+1)(m + 1, n)`.
The fourth identity additionally requires `k < n`, so that its right-hand side is in the
intended domain of `D_(k+1)`.

Source: Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal
of Integer Sequences 27 (2024), Article 24.1.8, Theorem 7
(`jis-2024-24.1.8-thm-7`). -/
public theorem_wanted genDelannoyLower_relations (k m n : ℕ) (hk : 1 ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    genDelannoyLower k m n + genDelannoyLower k m (n + 1) = 2 * genDelannoyLower (k - 1) m n ∧
      genDelannoyLower k m n + genDelannoyLower k (m + 1) n =
        genDelannoyLower (k + 1) (m + 1) (n + 1) ∧
      (genDelannoyLower k m (n + 1) : ℤ) - genDelannoyLower k m n =
        2 * genDelannoyLower (k - 1) (m - 1) n ∧
      (k < n → (genDelannoyLower k (m + 1) n : ℤ) - genDelannoyLower k m n =
        genDelannoyLower (k + 1) (m + 1) n)

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

end

end DelannoyConstructions

end MetaMathlibExt
