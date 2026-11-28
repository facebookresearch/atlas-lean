/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Tree.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import MathlibExt.Analysis.SpecialFunctions.TakagiFunction
public import MathlibExt.NumberTheory.Digits.BinaryDigitSum
public import MathlibExt.NumberTheory.TakagiDNodeEvenSuccessor
public import MathlibExt.NumberTheory.TakagiDNodeOddSuccessor
public import MathlibExt.NumberTheory.TakagiDNodeSuccessor
public import MathlibExt.NumberTheory.TakagiDNodeLevelPred
public import MathlibExt.NumberTheory.TakagiDyadicIdentities
public import MathlibExt.NumberTheory.TakagiDyadicSlope
public import MathlibExt.NumberTheory.TakagiDNodeTreeCount

/-!
# Takagi function identities on dyadic rationals

Statements from Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of
Integer Sequences 27 (2024), Article 24.2.7 (arXiv 2111.05996).

Conventions shared by all declarations below.

* The Takagi function `τ(r / 2^k)` is `takagiNewdef r (k - 1)`, the paper's own Definition
  `takagi_newdef` (already in `MathlibExt`), which evaluates `τ` at `n / 2^(k+1)`.
* Notation `not_n`: a positive integer is `n = 2^k + r` with `0 ≤ r < 2^k`, and `x = r / 2^k`.
* The binary digit `nᵢ` is `n / 2^i % 2`, the Hamming weight `s₁(n)` is
  `(Nat.digits 2 n).sum`, `⌊log₂ n⌋` is `Nat.log 2 n`, and the position `ρ₁` of the
  lowest nonzero bit of `r > 0` is `padicValNat 2 r`.
* `S₁(n) = ∑_{i<n} s₁(i)` is written out as a `Finset.range` sum.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **The Takagi function at dyadic rationals counts D-nodes (Coronado et al.).** Let $k$ and $r$
be natural numbers with $r \le 2^k$. Write $\tau(r / 2^k)$ for the Takagi value of the dyadic
presentation $r / 2^k$, and $\delta(n)$ for the number of $D$-nodes of the divide-and-conquer
tree on $n$ leaves, given by $\delta(1) = 0$, $\delta(2m) = 2 \delta(m)$ and
$\delta(2m + 1) = \delta(m) + \delta(m + 1) + 1$ for $m \ge 1$. Then
$\tau(r / 2^k) = \delta(2^k + r) / 2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 8 (`jis-2024-24.2.7-thm-8`). -/
public theorem_wanted takagi_dyadic_eq_dcDNodes_div (k r : ℕ) (hr : r ≤ 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) = (dcDNodes (2 ^ k + r) : ℝ) / 2 ^ k

/-- **Level-sum formula for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count. For every integer $n > 0$, let $k = \lfloor \log_2 n \rfloor$,
let $\lambda_i(n)$ be the level-$i$ D-node count, and let $n_i$ be the binary digit of $n$ at
$2^i$. Then
$$\delta(n) = \sum_{i=0}^{k-1} \lambda_i(n),$$
and explicitly
$$\delta(n) = \sum_{i=0}^{k-1} \left(n_i 2^i + (-1)^{n_i} (n \bmod 2^i)\right).$$

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 11 (`jis-2024-24.2.7-thm-11`). -/
public theorem_wanted dcDNodes_eq_sum_dcLevelDNodes (n : ℕ) (hn : 0 < n) :
    dcDNodes n = ∑ i ∈ range (Nat.log 2 n), dcLevelDNodes n i ∧
      (dcDNodes n : ℤ) =
        ∑ i ∈ range (Nat.log 2 n),
          (((n / 2 ^ i % 2 : ℕ) : ℤ) * 2 ^ i + (-1) ^ (n / 2 ^ i % 2) * ((n % 2 ^ i : ℕ) : ℤ))

/-- **Symmetry of the D-node counts.** For all natural numbers $k$ and $r$ with $r \le 2^k$,
$\delta(2^{k+1} - r) = \delta(2^k + r)$, where $\delta(n)$ denotes the number of D-nodes in the
divide-and-conquer tree on $n$ leaves.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 18 (`jis-2024-24.2.7-lem-18`). -/
public theorem_wanted dcDNodes_two_pow_succ_sub (k r : ℕ) (hr : r ≤ 2 ^ k) :
    dcDNodes (2 ^ (k + 1) - r) = dcDNodes (2 ^ k + r)

/-- **Binary-digit formula for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count and let $s_1(m)$ be the number of ones in the binary expansion
of $m$. For every integer $n > 0$, let $k = \lfloor \log_2 n \rfloor$ and let $n_j$ be the binary
digit of $n$ at $2^j$. Then
$$\delta(n) = \sum_{i=0}^{k-1} 2^i n_i \Big(k - i - 2 \sum_{j=i}^{k} n_j + 4\Big),$$
and also
$$\delta(n) = \sum_{i=0}^{k-1} 2^i n_i \Big(k - i - 2\, s_1(\lfloor n / 2^i \rfloor) + 4\Big).$$

The printed inner sum $\sum_{j=i}^k n_i$ is read as $\sum_{j=i}^k n_j$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 22 (`jis-2024-24.2.7-thm-22`). -/
public theorem_wanted dcDNodes_eq_sum_digit_weight (n : ℕ) (hn : 0 < n) :
    (dcDNodes n : ℤ) =
        ∑ i ∈ range (Nat.log 2 n),
          2 ^ i * ((n / 2 ^ i % 2 : ℕ) : ℤ) *
            ((Nat.log 2 n : ℤ) - i - 2 * ∑ j ∈ Icc i (Nat.log 2 n), ((n / 2 ^ j % 2 : ℕ) : ℤ) + 4) ∧
      (dcDNodes n : ℤ) =
        ∑ i ∈ range (Nat.log 2 n),
          2 ^ i * ((n / 2 ^ i % 2 : ℕ) : ℤ) *
            ((Nat.log 2 n : ℤ) - i - 2 * (Nat.digits 2 (n / 2 ^ i)).sum + 4)

/-- **Midpoint recurrence for the Takagi function at dyadic rationals.** Let $k$ and $r$ be
natural numbers with $1 \le r < 2^k$. For a natural number $m$, write $\tau(m / 2^k)$ for the
Takagi value of the dyadic presentation $m / 2^k$, and let $\rho_1$ be the $2$-adic valuation of
$r$, the position (counted from $0$) of the lowest nonzero binary digit of $r$. Then
$\tau(r / 2^k) = (\tau((r - 1) / 2^k) + \tau((r + 1) / 2^k))/2 + (1 - \rho_1)/2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 24 (`jis-2024-24.2.7-thm-24`). -/
public theorem_wanted takagi_dyadic_eq_midpoint_add (k r : ℕ) (hr0 : 1 ≤ r) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
      (takagiNewdef (r - 1) ((k : ℤ) - 1) + takagiNewdef (r + 1) ((k : ℤ) - 1)) / 2 +
        (1 - (padicValNat 2 r : ℝ)) / 2 ^ k

/-- **Takagi values at dyadic rationals from level $D$-node counts.** Let $k$ and $r$ be
natural numbers with $r < 2^k$ and put $n = 2^k + r$. Write $\tau(r, k-1)$ for the Takagi value
of the dyadic presentation $r/2^k$, write $n_i = \lfloor n/2^i \rfloor \bmod 2$ for the binary
digit of $n$ at position $i$, and let $\lambda_i(n)$ be the level-$i$ $D$-node count, which
equals $n \bmod 2^i$ if $n_i = 0$ and $2^i - (n \bmod 2^i)$ if $n_i = 1$. Then

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} \lambda_i(n)$$

and

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} (n_i 2^i + (-1)^{n_i} (n \bmod 2^i)).$$

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 25 (`jis-2024-24.2.7-thm-25`). -/
public theorem_wanted takagi_dyadic_eq_sum_dcLevelDNodes (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k, (dcLevelDNodes (2 ^ k + r) i : ℝ)) / 2 ^ k ∧
      takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k,
          (((((2 ^ k + r) / 2 ^ i % 2 : ℕ) : ℝ)) * 2 ^ i +
            (-1) ^ ((2 ^ k + r) / 2 ^ i % 2) * (((2 ^ k + r) % 2 ^ i : ℕ) : ℝ))) / 2 ^ k

/-- **Consecutive Takagi values at dyadic rationals.** Let $k$ and $r$ be natural numbers with
$r < 2^k$ and put $n = 2^k + r$. Write $\tau(m, k-1)$ for the Takagi value of the dyadic
presentation $m/2^k$, and $s_1(n)$ for the number of ones in the binary expansion of $n$. Then
$\tau(r+1, k-1) = \tau(r, k-1) + (k - 2 s_1(n) + 2)/2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 26 (`jis-2024-24.2.7-thm-26`). -/
public theorem_wanted takagi_dyadic_succ (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef (r + 1) ((k : ℤ) - 1) =
      takagiNewdef r ((k : ℤ) - 1) +
        ((k : ℝ) - 2 * (Nat.digits 2 (2 ^ k + r)).sum + 2) / 2 ^ k

/-- **Takagi values at dyadic rationals from binary digits.** Let $k$ and $r$ be natural
numbers with $r < 2^k$ and put $n = 2^k + r$. Write $\tau(r, k-1)$ for the Takagi value of the
dyadic presentation $r/2^k$, write $n_j = \lfloor n/2^j \rfloor \bmod 2$ for the binary digit of
$n$ at position $j$, and write $s_1(m)$ for the number of ones in the binary expansion of $m$.
Then

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} 2^i n_i (k - i - 2 \sum_{j=i}^{k} n_j + 4)$$

and

$$\tau(r, k-1) = 2^{-k} \sum_{i=0}^{k-1} 2^i n_i (k - i - 2 s_1(\lfloor n/2^i \rfloor) + 4).$$

The paper prints the inner sum as $\sum_{j=i}^{k} n_i$; it is read here as $\sum_{j=i}^{k} n_j$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 27 (`jis-2024-24.2.7-thm-27`). -/
public theorem_wanted takagi_dyadic_eq_sum_digit_weight (k r : ℕ) (hr : r < 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k,
          2 ^ i * (((2 ^ k + r) / 2 ^ i % 2 : ℕ) : ℝ) *
            ((k : ℝ) - i - 2 * ∑ j ∈ Icc i k, (((2 ^ k + r) / 2 ^ j % 2 : ℕ) : ℝ) + 4)) /
          2 ^ k ∧
      takagiNewdef r ((k : ℤ) - 1) =
        (∑ i ∈ range k,
          2 ^ i * (((2 ^ k + r) / 2 ^ i % 2 : ℕ) : ℝ) *
            ((k : ℝ) - i - 2 * (Nat.digits 2 ((2 ^ k + r) / 2 ^ i)).sum + 4)) / 2 ^ k

/-- **Trollope's formula via the Takagi function.** For a natural number $m$, write $s_1(m)$ for
the sum of the binary digits of $m$ and $S_1(m) = \sum_{i=0}^{m-1} s_1(i)$. Let $k$ and $r$ be
natural numbers with $r < 2^k$, and put $n = 2^k + r$ and $x = r / 2^k$. Write $\tau(x)$ for
the Takagi value of the dyadic presentation $r / 2^k$. Then

$$S_1(n) = \frac{n \log_2 n}{2} + 2^{k-1} \left(2x - \tau(x) - (1 + x) \log_2 (1 + x)\right).$$

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 30 (`jis-2024-24.2.7-cor-30`). -/
public theorem_wanted sum_hammingWeight_range_eq_trollope (k r : ℕ) (hr : r < 2 ^ k) :
    ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
      ((2 ^ k + r : ℕ) : ℝ) * Real.logb 2 ((2 ^ k + r : ℕ) : ℝ) / 2 +
        2 ^ k / 2 *
          (2 * ((r : ℝ) / 2 ^ k) - takagiNewdef r ((k : ℤ) - 1) -
            (1 + (r : ℝ) / 2 ^ k) * Real.logb 2 (1 + (r : ℝ) / 2 ^ k))

/-- **Cumulative binary digit sums via the Takagi function.** For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ and $S_1(m) = \sum_{i=0}^{m-1} s_1(i)$. Let
$k$ and $r$ be natural numbers with $r < 2^k$, and put $n = 2^k + r$ and $x = r / 2^k$. Write
$\tau(x)$ for the Takagi value of the dyadic presentation $r / 2^k$, and $\delta(n)$ for the
number of $D$-nodes of the divide-and-conquer tree on $n$ leaves, given by $\delta(1) = 0$,
$\delta(2m) = 2 \delta(m)$ and $\delta(2m + 1) = \delta(m) + \delta(m + 1) + 1$ for $m \ge 1$.
Then $S_1(n) = (nk + 2^k (2x - \tau(x)))/2$, $S_1(n) = (nk + 2r - 2^k \tau(x))/2$ and
$S_1(n) = (nk + 2r - \delta(n))/2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Corollary 31 (`jis-2024-24.2.7-cor-31`). -/
public theorem_wanted sum_hammingWeight_range_eq_takagi_dcDNodes (k r : ℕ) (hr : r < 2 ^ k) :
    ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
        (((2 ^ k + r : ℕ) : ℝ) * k +
          2 ^ k * (2 * ((r : ℝ) / 2 ^ k) - takagiNewdef r ((k : ℤ) - 1))) / 2 ∧
      ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
        (((2 ^ k + r : ℕ) : ℝ) * k + 2 * r - 2 ^ k * takagiNewdef r ((k : ℤ) - 1)) / 2 ∧
      ((∑ i ∈ range (2 ^ k + r), (Nat.digits 2 i).sum : ℕ) : ℝ) =
        (((2 ^ k + r : ℕ) : ℝ) * k + 2 * r - dcDNodes (2 ^ k + r)) / 2

end

end MetaMathlibExt
