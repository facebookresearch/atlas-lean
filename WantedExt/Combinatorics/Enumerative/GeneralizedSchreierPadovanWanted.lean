/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Div
public import MathlibExt.Combinatorics.Enumerative.MaximalSchreierCount
public import MathlibExt.Combinatorics.Enumerative.MaximalSchreierCountDifference

/-!
# Generalized Schreier sets and Padovan-like sequences

Statements from Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized
Schreier Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2. For positive
integers `p, q`, a finite nonempty set `F` of positive integers is `(p, q)`-Schreier if
`q min F ≥ p |F|` and maximal `(p, q)`-Schreier if `q min F = p |F|`; `S^{p/q}_n` and
`M^{p/q}_n` collect those with `max F = n`. Their counts are taken `q`-periodically from the
Padovan-like sequences `a_{p,q,n}` and `a^{(m)}_{p,q,n}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Schreier counts as Padovan-like sequences.** Write $a_{p,q,k}$ and $a^{(m)}_{p,q,k}$ for the
Padovan-like sequences for Schreier sets and for maximal Schreier sets. For positive integers $p$,
$q$ and $n$, the number $|S^{p/q}_n|$ of $(p, q)$-Schreier sets with maximum $n$ equals
$a_{p,q,(n-1)q}$, and the number $|M^{p/q}_n|$ of maximal $(p, q)$-Schreier sets with maximum $n$
equals $a^{(m)}_{p,q,(n-1)q}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 1
(`jis-2026-26.2.2-thm-1`). -/
public theorem_wanted schreierCount_eq_schreierPadovan {p q n : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hn : 1 ≤ n) :
    schreierCount p q n = schreierPadovan p q ((n - 1) * q) ∧
      maximalSchreierCount p q n = maximalSchreierPadovan p q ((n - 1) * q)

/-- **Closed formula and recurrence for Schreier counts.** Let $p$ and $q$ be positive integers,
and write $|S^{p/q}_n|$ for the number of $(p, q)$-Schreier sets with maximum $n$. For every
natural number $n$,

$$|S^{p/q}_n| = \sum_{i=1}^{\lfloor (n+1)q/(p+q) \rfloor} \binom{n - \lceil pi/q \rceil}{i - 1},$$

and for every $n \ge p + q + 1$,

$$|S^{p/q}_n| = \sum_{i=1}^{q} (-1)^{i+1} \binom{q}{i} |S^{p/q}_{n-i}| + |S^{p/q}_{n-(p+q)}|.$$

The printed initial-term formula has $\lceil ni/q \rceil$ in place of $\lceil pi/q \rceil$, which is
false (for $p = 1$, $q = 2$, $n = 2$ one has $|S^{1/2}_2| = 2$ but the printed sum is $1$);
$\lceil pi/q \rceil$ is the paper's own formula (Section 3, equation for $|S^{p/q}_n|$). The
corollary states the formula for $1 \le n \le p + q$; it holds for every $n$, so the range
restriction is dropped.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Corollary 2
(`jis-2026-26.2.2-cor-2`). -/
public theorem_wanted schreierCount_formula_and_recurrence {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∀ n, schreierCount p q n =
      ∑ i ∈ Finset.Icc 1 ((n + 1) * q / (p + q)), (n - (p * i + q - 1) / q).choose (i - 1)) ∧
    ∀ n, p + q + 1 ≤ n →
      (schreierCount p q n : ℤ) =
        ∑ i ∈ Finset.Icc 1 q, (-1) ^ (i + 1) * (q.choose i : ℤ) * schreierCount p q (n - i) +
          schreierCount p q (n - (p + q))

end

end MetaMathlibExt
