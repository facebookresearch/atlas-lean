/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic

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

/-- **Number of (p, q)-Schreier sets with given maximum.** For natural numbers $p$, $q$ and $n$,
$|S^{p/q}_n|$ is the number of $(p, q)$-Schreier sets with maximum $n$, that is, of subsets
$F \subseteq \{1, \dots, n\}$ with $n \in F$ and $p|F| \le qx$ for every $x \in F$ (equivalently,
$p|F| \le q \min F$).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def schreierCount (p q n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun F => n ∈ F ∧ ∀ x ∈ F, p * F.card ≤ q * x).card

/-- **Number of maximal $(p, q)$-Schreier sets.** For natural numbers $p$, $q$ and $n$,
$|M^{p/q}_n|$ is the number of maximal $(p, q)$-Schreier sets with maximum $n$, that is, of sets
$F \subseteq \{1, \dots, n\}$ with $n \in F$ and $q \min F = p |F|$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def maximalSchreierCount (p q n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun F =>
    n ∈ F ∧ (∀ x ∈ F, p * F.card ≤ q * x) ∧ ∃ x ∈ F, q * x = p * F.card).card

/-- **Padovan-like sequence for Schreier sets.** For natural numbers $p$ and $q$, the sequence
$a_{p,q,n}$, $n \ge 0$, is defined as follows. If $q \ge 1$ and $n \ge p + q$, then
$a_{p,q,n} = a_{p,q,n-q} + a_{p,q,n-p-q}$. Otherwise, if $p \ge q$, then $a_{p,q,n} = 0$ for
$n < p - q$ and $a_{p,q,n} = 1$ for $n \ge p - q$; and if $p < q$, then $a_{p,q,n} = 1$ for
$n < 2p$ and $a_{p,q,n} = 2$ for $n \ge 2p$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def schreierPadovan (p q : ℕ) : ℕ → ℕ
  | n =>
    if _h : p + q ≤ n ∧ 0 < q then
      schreierPadovan p q (n - q) + schreierPadovan p q (n - p - q)
    else if q ≤ p then (if n + q < p then 0 else 1) else (if n < 2 * p then 1 else 2)
  decreasing_by all_goals omega

/-- **Padovan-like sequence of maximal Schreier sets.** For natural numbers $p$ and $q$, the
sequence $a^{(m)}_{p,q,n}$, $n \ge 0$, is defined as follows. If $q \ge 1$ and $n \ge p + q$, then
$a^{(m)}_{p,q,n} = a^{(m)}_{p,q,n-q} + a^{(m)}_{p,q,n-p-q}$. Otherwise, if $q \le p$, then
$a^{(m)}_{p,q,n}$ is $1$ for $n = p - q$ and $0$ for every other $n$, and if $p < q$, then
$a^{(m)}_{p,q,n}$ is $1$ for $n = 2p$ and $0$ for every other $n$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def maximalSchreierPadovan (p q : ℕ) : ℕ → ℕ
  | n =>
    if _h : p + q ≤ n ∧ 0 < q then
      maximalSchreierPadovan p q (n - q) + maximalSchreierPadovan p q (n - p - q)
    else if q ≤ p then (if n + q = p then 1 else 0) else (if n = 2 * p then 1 else 0)
  decreasing_by all_goals omega

/-- **Recurrence for the Padovan-like sequence.** For natural numbers $p$, $q$ and $n$ with
$q \ge 1$ and $n \ge p + q$, the Padovan-like sequence satisfies
$a_{p,q,n} = a_{p,q,n-q} + a_{p,q,n-p-q}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
theorem schreierPadovan_rec {p q n : ℕ} (hq : 0 < q) (hn : p + q ≤ n) :
    schreierPadovan p q n = schreierPadovan p q (n - q) + schreierPadovan p q (n - p - q) := by
  rw [schreierPadovan]
  simp only [hn, hq, and_self, ↓reduceDIte]

/-- **Recurrence for the Padovan-like sequence of maximal Schreier sets.** For natural numbers
$p$, $q$ and $n$ with $q \ge 1$ and $n \ge p + q$, the Padovan-like sequence $a^{(m)}_{p,q,n}$ of
maximal Schreier sets satisfies $a^{(m)}_{p,q,n} = a^{(m)}_{p,q,n-q} + a^{(m)}_{p,q,n-p-q}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
theorem maximalSchreierPadovan_rec {p q n : ℕ} (hq : 0 < q) (hn : p + q ≤ n) :
    maximalSchreierPadovan p q n =
      maximalSchreierPadovan p q (n - q) + maximalSchreierPadovan p q (n - p - q) := by
  rw [maximalSchreierPadovan]
  simp only [hn, hq, and_self, ↓reduceDIte]

/-- **Small values of the Padovan-like sequences.** For $n = 0, 1, \dots, 7$, the Padovan-like
sequence $a_{1,2,n}$ takes the values $1, 1, 2, 2, 3, 4, 5, 7$, and $a_{2,1,n}$ takes the values
$0, 1, 1, 1, 2, 3, 4, 6$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Table 3. -/
theorem schreierPadovan_small :
    (List.range 8).map (schreierPadovan 1 2) = [1, 1, 2, 2, 3, 4, 5, 7] ∧
      (List.range 8).map (schreierPadovan 2 1) = [0, 1, 1, 1, 2, 3, 4, 6] := by
  decide +kernel

/-- **First values of the Padovan-like sequences of maximal Schreier sets.** For
$n = 0, 1, \dots, 7$, the Padovan-like sequence $a^{(m)}_{1,2,n}$ of maximal Schreier sets takes
the values $0, 0, 1, 0, 1, 1, 1, 2$, and $a^{(m)}_{2,1,n}$ takes the values
$0, 1, 0, 0, 1, 1, 1, 2$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Table 4. -/
theorem maximalSchreierPadovan_small :
    (List.range 8).map (maximalSchreierPadovan 1 2) = [0, 0, 1, 0, 1, 1, 1, 2] ∧
      (List.range 8).map (maximalSchreierPadovan 2 1) = [0, 1, 0, 0, 1, 1, 1, 2] := by
  decide +kernel

/-- **Small values of the (1, 2)-Schreier counts.** For $n = 1, 2, 3, 4$, the number $|S^{1/2}_n|$
of $(1, 2)$-Schreier sets with maximum $n$ takes the values $1, 2, 3, 5$, and the number
$|M^{1/2}_n|$ of maximal $(1, 2)$-Schreier sets with maximum $n$ takes the values $0, 1, 1, 1$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Tables 1 and 2. -/
theorem schreierCount_one_two_small :
    (List.range 4).map (fun n => schreierCount 1 2 (n + 1)) = [1, 2, 3, 5] ∧
      (List.range 4).map (fun n => maximalSchreierCount 1 2 (n + 1)) = [0, 1, 1, 1] := by
  decide +kernel

/-- **Sequences satisfying a polynomial.** Let $P = c_0 + c_1 x + \dots + c_r x^r$ be a real
polynomial, where $r$ is the degree of $P$ (and $r = 0$ for $P = 0$). A real sequence
$(a_n)_{n \ge 0}$ satisfies $P$ if $c_0 a_n + c_1 a_{n-1} + \dots + c_r a_{n-r} = 0$ for every
$n \ge r$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 4, Definition 4. -/
def SatisfiesPoly (P : Polynomial ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ n, P.natDegree ≤ n → ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * a (n - i) = 0

/-- **Every sequence satisfies the zero polynomial.** Every real sequence $(a_n)_{n \ge 0}$
satisfies the zero polynomial.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 4, Definition 4. -/
theorem satisfiesPoly_zero (a : ℕ → ℝ) : SatisfiesPoly 0 a := by
  intro n _
  simp

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

/-- **A sequence satisfying a polynomial satisfies its multiples.** Let $P$ and $Q$ be real
polynomials with $P \mid Q$. If a real sequence $(a_n)_{n \ge 0}$ satisfies $P$, then it
satisfies $Q$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Lemma 5
(`jis-2026-26.2.2-lem-5`). -/
public theorem_wanted SatisfiesPoly.of_dvd {P Q : Polynomial ℝ} {a : ℕ → ℝ}
    (h : SatisfiesPoly P a) (hPQ : P ∣ Q) : SatisfiesPoly Q a

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
