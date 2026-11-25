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

end

end MetaMathlibExt
