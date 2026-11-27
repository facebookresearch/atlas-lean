/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Digits.BasePhiRepresentations
public import MathlibExt.NumberTheory.Digits.BergmanLucasEvenAdd
public import MathlibExt.NumberTheory.Digits.BergmanLucasOddAdd
public import MathlibExt.NumberTheory.Digits.BergmanWordFib
public import MathlibExt.NumberTheory.Digits.FibMemLucasIntervals
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Digits.BasePhiRepresentationsBergmanLowestPositionLucasInterval

/-!
# Counting base phi representations

Statements from Michel Dekking and Ad van Loon, *Counting Base Phi
Representations*, Fibonacci Quarterly 62 (2024), no. 2, 112-124.

A finite base phi expansion with digits `0` and `1` is encoded by the finite set
`S : Finset ℤ` of positions of its digits `1`; it represents
`∑ i ∈ S, φ ^ i`. The word `B(N)` of the paper is the digit word of `S` read from
the highest to the lowest position, so a statement about `B(N)` alone is a
statement about `S` up to translation.
-/

namespace MetaMathlibExt

/-- **Recursion for the number of Knott expansions.** Let $\varphi$ be the golden ratio, let
$N \ge 2$ and $n$ be natural numbers, and let $p_0, \dots, p_n$ be integers with
$p_{k+1} \ge p_k + 2$ for all $k < n$ and $\sum_{k=0}^{n} \varphi^{p_k} = N$. Thus $N$ has the
base phi expansion $10^{s_n} \cdots 10^{s_1} 1$ with digits $1$ at positions $p_0 < \dots < p_n$,
where $s_k = p_k - p_{k-1} - 1$ for $1 \le k \le n$. Let $r_0, r_1, \dots$ be integers with
$r_0 = 1$; if $n \ge 1$, let $r_1 = s_1/2 + 1$ when $s_1$ is even and $r_1 = (s_1 + 1)/2 + 1$
when $s_1$ is odd; and for $2 \le k \le n$, let $r_k = (s_k/2 + 1)\, r_{k-1}$ when $s_k$ is even
and $r_k = ((s_k + 1)/2 + 1)\, r_{k-1} - r_{k-2}$ when $s_k$ is odd. Then the number of Knott
expansions of $N$ is $r_n$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 2.3
(`fq-2024-dekking11102023-thm-2.3`). -/
public theorem_wanted knottExpansionCount_eq_of_recursion (N : ℕ) (hN : 2 ≤ N) (n : ℕ)
    (p : ℕ → ℤ) (hgap : ∀ k < n, p k + 2 ≤ p (k + 1))
    (hval : basePhiValue ((Finset.range (n + 1)).image p) = N)
    (s : ℕ → ℤ) (hs : ∀ k, 1 ≤ k → k ≤ n → s k = p k - p (k - 1) - 1)
    (r : ℕ → ℤ) (hr0 : r 0 = 1)
    (hr1 : 1 ≤ n → (Even (s 1) → 2 * r 1 = s 1 + 2) ∧ (Odd (s 1) → 2 * r 1 = s 1 + 3))
    (hr : ∀ k, 2 ≤ k → k ≤ n →
      (Even (s k) → 2 * r k = (s k + 2) * r (k - 1)) ∧
      (Odd (s k) → 2 * r k = (s k + 3) * r (k - 1) - 2 * r (k - 2))) :
    (knottExpansionCount N : ℤ) = r n

/-- **Knott expansions of Fibonacci numbers.** Let $F_n$ be the Fibonacci numbers ($F_0 = 0$,
$F_1 = 1$). For every $n \ge 1$, the number of Knott expansions of $F_n$ is $F_n$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 3.2
(`fq-2024-dekking11102023-thm-3.2`). -/
public theorem_wanted knottExpansionCount_fib (n : ℕ) (hn : 1 ≤ n) :
    knottExpansionCount (Nat.fib n) = Nat.fib n

/-- **Knott expansions of Lucas numbers.** For every $n \ge 1$, each of the Lucas numbers $L_{2n}$
and $L_{2n+1}$ (with $L_0 = 2$, $L_1 = 1$) has exactly $2n + 1$ Knott expansions.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 3.3
(`fq-2024-dekking11102023-thm-3.3`). -/
public theorem_wanted knottExpansionCount_lucasNumber (n : ℕ) (hn : 1 ≤ n) :
    knottExpansionCount (lucasNumber (2 * n)) = 2 * n + 1 ∧
      knottExpansionCount (lucasNumber (2 * n + 1)) = 2 * n + 1

/-- **Recursion for the number of natural expansions.** Let $N$ and $n$ be natural numbers and
let $p_0, \dots, p_n$ be integers with $p_k + 2 \le p_{k+1}$ for $k < n$ such that the base phi
expansion with digits $1$ at positions $p_0, \dots, p_n$ represents $N$. Put
$s_k = p_k - p_{k-1} - 1$ for $1 \le k \le n$. Let $r_0, r_1, \dots$ be integers with
$r_0 = 1$ such that, if $n \ge 1$, $2 r_1 = s_1 + 2$ when $s_1$ is even and $2 r_1 = s_1 + 1$
when $s_1$ is odd, and for $2 \le k \le n$, $2 r_k = (s_k + 2) r_{k-1}$ when $s_k$ is even and
$2 r_k = (s_k + 3) r_{k-1} - 2 r_{k-2}$ when $s_k$ is odd. Then the number
$\mathrm{Tot}_\nu(N)$ of natural base phi expansions of $N$ equals $r_n$.

Compared with the recursion for the number of Knott expansions, only the value of $r_1$ for odd
$s_1$ differs, and $N \ge 2$ is not assumed.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.1
(`fq-2024-dekking11102023-thm-4.1`). -/
public theorem_wanted naturalExpansionCount_eq_of_recursion (N : ℕ) (n : ℕ)
    (p : ℕ → ℤ) (hgap : ∀ k < n, p k + 2 ≤ p (k + 1))
    (hval : basePhiValue ((Finset.range (n + 1)).image p) = N)
    (s : ℕ → ℤ) (hs : ∀ k, 1 ≤ k → k ≤ n → s k = p k - p (k - 1) - 1)
    (r : ℕ → ℤ) (hr0 : r 0 = 1)
    (hr1 : 1 ≤ n → (Even (s 1) → 2 * r 1 = s 1 + 2) ∧ (Odd (s 1) → 2 * r 1 = s 1 + 1))
    (hr : ∀ k, 2 ≤ k → k ≤ n →
      (Even (s k) → 2 * r k = (s k + 2) * r (k - 1)) ∧
      (Odd (s k) → 2 * r k = (s k + 3) * r (k - 1) - 2 * r (k - 2))) :
    (naturalExpansionCount N : ℤ) = r n

/-- **Natural expansions are counted by Fibonacci representations.** Write $F_k$ for the $k$-th
Fibonacci number. Let $N > 3$ be a natural number, let $S$ be a Bergman expansion of $N$ and let
$R$ be the lowest position of a digit $1$ in $S$. Then the number $\mathrm{Tot}_\nu(N)$ of natural
base phi expansions of $N$ equals the number $\mathrm{Tot}_{\mathrm{FIB}}(F_{2-R} N)$ of
representations of $F_{2-R} N$ as a sum of Fibonacci numbers with distinct indices at least $2$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.4
(`fq-2024-dekking11102023-thm-4.4`). -/
public theorem_wanted naturalExpansionCount_eq_fibonacciRepresentationCount (N : ℕ)
    (hN : 3 < N) {S : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N)
    {R : ℤ} (hR : IsLeast (S : Set ℤ) R) :
    naturalExpansionCount N = fibonacciRepresentationCount (Nat.fib (2 - R).toNat * N)

/-- **Lucas interval of $N$ from the gap between its two lowest Bergman digits.** Let $N \ge 2$
be a natural number, let $S$ be a finite set of integers with no two consecutive elements (a
Bergman expansion) whose base phi value is $N$, and let $a$ be an integer and $s$ a natural number
such that the elements of $S$ that are at most $a + s + 1$ are exactly $a$ and $a + s + 1$ (so the
expansion ends in the digits $10^s1$). Write $L_m$ for the $m$-th Lucas number. Then
$L_{2n} \le N \le L_{2n+1}$ for some natural number $n$ if and only if $s$ is odd, and
$L_{2n+1} + 1 \le N \le L_{2n+2} - 1$ for some natural number $n$ if and only if $s$ is even.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 5.1(a)
(`fq-2024-dekking11102023-prop-5.1`). -/
public theorem_wanted bergman_tail_parity_iff_lucasInterval (N : ℕ) (hN : 2 ≤ N)
    {S : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N) (a : ℤ) (s : ℕ)
    (htail : S.filter (· ≤ a + s + 1) = {a, a + s + 1}) :
    ((∃ n : ℕ, N ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1))) ↔ Odd s) ∧
      ((∃ n : ℕ, N ∈ Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1)) ↔
        Even s)

end MetaMathlibExt
