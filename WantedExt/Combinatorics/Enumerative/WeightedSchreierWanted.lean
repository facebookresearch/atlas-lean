/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.WeightedSchreier

/-!
# Weighted Schreier-type sets and the Fibonacci sequence

Statements from Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4.

For `k ∈ ℕ` and a finite set `E` of positive integers, `ω_k(E)` counts the elements of `E`
other than `k`, and `a_{k,n}` counts the sets `E ⊆ {1, …, n}` that are empty or satisfy
`ω_k(E) < min E`. The condition `ω_k(E) < min E` is encoded as `ω_k(E) < m` for every `m ∈ E`,
which is vacuous for `E = ∅`. The definitions and the iterated partial sums of Section 3 are
taken from the arXiv version (arXiv:2405.19352v1), whose Section 3 numbering is shifted
against the journal labels used below: journal Proposition 3.1 is arXiv Proposition 3.2,
journal Lemmas 3.2-3.4 are arXiv Lemmas 3.3-3.5, and journal Proposition 3.5 is arXiv
Proposition 3.1.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Diagonal weighted Schreier counts.** For every natural number $n \ge 1$, the weighted
Schreier count satisfies $a_{n,n} = 2F_n$, where $F_n$ is the $n$-th Fibonacci number
($F_0 = 0$, $F_1 = 1$).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.1
(`fq-2024-chu08302024rev-thm-1.1`). -/
public theorem_wanted weightedSchreierCount_diag {n : ℕ} (hn : 1 ≤ n) :
    weightedSchreierCount n n = 2 * Nat.fib n

/-- **Weighted Schreier counts on and above the diagonal.** Let $a_{k,n}$ be the weighted
Schreier count and let $F_n$ denote the Fibonacci numbers, with $F_0 = 0$ and $F_1 = 1$. For all
$k \ge 2$ and $\ell \ge 0$,
$a_{k,k+\ell} = 2\sum_{i=0}^{k-2} \binom{\ell}{i} F_{k-i} + 2\binom{\ell}{k-1} +
\sum_{j=1}^{\ell} \binom{j}{\ell-j+k}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.2, case `k ≥ 2`,
`ℓ ≥ 0` (`fq-2024-chu08302024rev-thm-1.2`). -/
public theorem_wanted weightedSchreierCount_add {k : ℕ} (hk : 2 ≤ k) (l : ℕ) :
    weightedSchreierCount k (k + l) =
      2 * ∑ i ∈ Finset.range (k - 1), l.choose i * Nat.fib (k - i) + 2 * l.choose (k - 1) +
        ∑ j ∈ Finset.Icc 1 l, j.choose (l - j + k)

/-- **Weighted Schreier counts for $0 < m < k$.** For natural numbers $k \ge 2$ and $m$ with
$0 < m < k$, the weighted Schreier count satisfies $a_{k,m} = F_{m+1}$, where $F_j$ is the
$j$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.2, case `k ≥ 2`,
`-k < ℓ < 0` (`fq-2024-chu08302024rev-thm-1.2`). -/
public theorem_wanted weightedSchreierCount_of_pos_of_lt {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (hmk : m < k) : weightedSchreierCount k m = Nat.fib (m + 1)

/-- **Weighted Schreier counts equal twice a Fibonacci number for small offsets.** Let
$a_{k,n}$ be the weighted Schreier count and let $F_n$ denote the Fibonacci numbers, with
$F_0 = 0$ and $F_1 = 1$. For all $k, \ell \ge 0$ with $k \ge \ell + 2$, we have
$a_{k,k+\ell} = 2F_{k+\ell}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.4
(`fq-2024-chu08302024rev-thm-1.4`). -/
public theorem_wanted weightedSchreierCount_add_of_le {k l : ℕ} (hkl : l + 2 ≤ k) :
    weightedSchreierCount k (k + l) = 2 * Nat.fib (k + l)

/-- **Recurrence for weighted Schreier counts.** For natural numbers $k$ and $n$ with $k \ge 1$,
$n > k$ and $n > 2$, the weighted Schreier counts satisfy $a_{k,n} = a_{k,n-1} + a_{k-1,n-2}$.
At $k = 1$ the term $a_{0,n-2}$ is the same count with $\omega_0(E)$, the number of elements of
$E$ different from $0$, equal to the number $|E|$ of all elements of $E$, since no element of a
set $E \subseteq \{1, \dots, n-2\}$ equals $0$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Proposition 3.1
(`fq-2024-chu08302024rev-prop-3.1`). -/
public theorem_wanted weightedSchreierCount_recurrence {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (h2n : 2 < n) :
    weightedSchreierCount k n =
      weightedSchreierCount k (n - 1) + weightedSchreierCount (k - 1) (n - 2)

/-- **Effect of the seed on seeded partial sums.** Let $R$ be a commutative ring, let
$a = (a_n)_{n \ge 0}$ and $b = (b_n)_{n \ge 0}$ be sequences in $R$, and write $t^b_{k,n}$ for
the seeded partial sums of $a$ with seed sequence $b$ and $t^0_{k,n}$ for those with the zero
seed sequence. Then for all $k, n \ge 0$,
$t^b_{k,n} - t^0_{k,n} = \sum_{i<k} \binom{n}{i} b_{k-1-i}$, where the binomial coefficients
are read as elements of $R$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.2
(`fq-2024-chu08302024rev-lem-3.2`). -/
public theorem_wanted seededPartialSums_sub_zero {R : Type*} [CommRing R] (b a : ℕ → R)
    (k n : ℕ) :
    seededPartialSums b a k n - seededPartialSums 0 a k n =
      ∑ i ∈ Finset.range k, (n.choose i : R) * b (k - 1 - i)

/-- **Adding one to a sequence shifts its iterated partial sums by a binomial coefficient.**
Let $R$ be a commutative ring, let $(a_n)_{n \ge 0}$ be a sequence in $R$, and let $k, m \ge 0$.
Writing $P^{(k)}(x)(m)$ for the $k$-fold iterated partial sum of a sequence $x$ at $m$, we have
$P^{(k)}((a_n + 1)_{n \ge 0})(m) - P^{(k)}((a_n)_{n \ge 0})(m) = \binom{m}{k}$, where
$\binom{m}{k}$ is read as an element of $R$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.3
(`fq-2024-chu08302024rev-lem-3.3`). -/
public theorem_wanted iteratedPartialSum_add_one_sub {R : Type*} [CommRing R] (a : ℕ → R)
    (k m : ℕ) :
    iteratedPartialSum k (fun n => a n + 1) m - iteratedPartialSum k a m = (m.choose k : R)

/-- **Iterated partial sums of shifted Fibonacci numbers.** Let $F_n$ denote the Fibonacci
numbers, with $F_0 = 0$ and $F_1 = 1$, and write $P^{(k)}(x)(m)$ for the $k$-fold iterated
partial sum of a sequence $x$ of natural numbers at $m$. Then for all $k, \ell \ge 0$,
$P^{(k)}((F_{n+2})_{n \ge 0})(\ell) = P^{(k)}((F_n)_{n \ge 0})(\ell) +
P^{(k)}((F_n)_{n \ge 0})(\ell + 1)$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.4
(`fq-2024-chu08302024rev-lem-3.4`). -/
public theorem_wanted iteratedPartialSum_fib_add_two (k l : ℕ) :
    iteratedPartialSum k (fun n => Nat.fib (n + 2)) l =
      iteratedPartialSum k Nat.fib l + iteratedPartialSum k Nat.fib (l + 1)

/-- **Weighted Schreier counts for $n < k$.** For all natural numbers $n < k$, the weighted
Schreier count satisfies $a_{k,n} = F_{n+1}$, where $F_j$ is the $j$-th Fibonacci number
($F_0 = 0$, $F_1 = 1$).

This includes $n = 0$, where $a_{k,0} = 1 = F_1$; the source takes $n$ positive.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Proposition 3.5
(`fq-2024-chu08302024rev-prop-3.5`). -/
public theorem_wanted weightedSchreierCount_of_lt {k n : ℕ} (hnk : n < k) :
    weightedSchreierCount k n = Nat.fib (n + 1)

end

end MetaMathlibExt
