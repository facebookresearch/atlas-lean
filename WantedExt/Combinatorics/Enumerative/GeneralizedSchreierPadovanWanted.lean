/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Div
public import MathlibExt.Combinatorics.Enumerative.GeneralizedSchreierPadovan

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

/-- **Closed form and recurrence for maximal $(p, q)$-Schreier sets.** Let $p$ and $q$ be positive
integers, put $p' = p / \gcd(p, q)$ and $q' = q / \gcd(p, q)$, and for each $n$ let
$|M^{p/q}_n|$ be the number of maximal $(p, q)$-Schreier sets with maximum $n$, that is, of sets
$F \subseteq \{1, \dots, n\}$ with $n \in F$ and $q \min F = p |F|$. For each $n$, let $K_n$ be
the set of integers $k$ with $1 \le k \le \lfloor (n+1)/(p'+q') \rfloor$ and $q'k \ge 2$, and let
$\delta_n$ be $1$ if $q' = 1$ and $n = p'$, and $0$ otherwise. Then for every $n \ge 0$,

$$|M^{p/q}_n| = \sum_{k \in K_n} \binom{n - p'k - 1}{q'k - 2} + \delta_n,$$

and for every $n \ge p + q + 1$,

$$|M^{p/q}_n| = \sum_{i=1}^{q} (-1)^{i+1} \binom{q}{i} |M^{p/q}_{n-i}| + |M^{p/q}_{n-(p+q)}|.$$

The paper prints the first formula as a sum over all $1 \le k \le \lfloor (n+1)/(p'+q') \rfloor$,
without $\delta_n$, and only for $1 \le n \le p + q$. Read with binomial coefficients vanishing
at negative lower index, it fails at $p = q = n = 1$, where $|M^{1/1}_1| = 1$ but the sum is $0$;
the term $\delta_n$ counts the singleton $\{n\}$, as in equation (10) of the paper's proof of
Theorem 1.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Corollary 3
(`jis-2026-26.2.2-cor-3`). -/
public theorem_wanted maximalSchreierCount_formula_and_recurrence {p q : ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) :
    (∀ n, maximalSchreierCount p q n =
      ∑ k ∈ (Finset.Icc 1 ((n + 1) / (p / p.gcd q + q / p.gcd q))).filter
          (fun k => 2 ≤ q / p.gcd q * k),
        (n - p / p.gcd q * k - 1).choose (q / p.gcd q * k - 2) +
      if q / p.gcd q = 1 ∧ n = p / p.gcd q then 1 else 0) ∧
    ∀ n, p + q + 1 ≤ n →
      (maximalSchreierCount p q n : ℤ) =
        ∑ i ∈ Finset.Icc 1 q,
            (-1) ^ (i + 1) * (q.choose i : ℤ) * maximalSchreierCount p q (n - i) +
          maximalSchreierCount p q (n - (p + q))

/-- **Counting $(p, 1)$-Schreier sets by maximal $(p, 1)$-Schreier sets.** Fix a positive integer
$p$. For each $m$, let $|S^{p/1}_m|$ be the number of sets $F \subseteq \{1, \dots, m\}$ with
$m \in F$ and $\min F \ge p |F|$, and let $|M^{p/1}_m|$ be the number of those with
$\min F = p |F|$. Then $|S^{p/1}_n| = |M^{p/1}_{n+p+1}|$ for every natural number $n$.

The paper states this for $n \ge 1$; at $n = 0$ both sides are $0$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 8
(`jis-2026-26.2.2-thm-8`). -/
public theorem_wanted schreierCount_eq_maximalSchreierCount_add {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    schreierCount p 1 n = maximalSchreierCount p 1 (n + p + 1)

/-- **Maximal $(1, q)$-Schreier sets counted by $(1, q)$-Schreier sets.** Fix a positive integer
$q$. For each $m$, let $|S^{1/q}_m|$ be the number of sets $F \subseteq \{1, \dots, m\}$ with
$m \in F$ and $q \min F \ge |F|$, and let $|M^{1/q}_m|$ be the number of those with
$q \min F = |F|$. Then $|M^{1/q}_n| = 2|S^{1/q}_n| - |S^{1/q}_{n+1}|$ for every positive integer
$n$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 9
(`jis-2026-26.2.2-thm-9`). -/
public theorem_wanted maximalSchreierCount_eq_two_mul_sub {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (maximalSchreierCount 1 q n : ℤ) = 2 * schreierCount 1 q n - schreierCount 1 q (n + 1)

end

end MetaMathlibExt
