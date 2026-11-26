/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.LiminfLimsup
public import MathlibExt.Combinatorics.Enumerative.TotienomialCoefficient
public import MathlibExt.NumberTheory.BinomidAverage
public import MathlibExt.NumberTheory.BinomidPartialSum
public import MathlibExt.NumberTheory.BinomidPrimeDivisibility
public import MathlibExt.NumberTheory.GeneralizedFibocatalanNumber
public import MathlibExt.NumberTheory.PrimeDvdChoose
public import MathlibExt.NumberTheory.BinomidIndexAdd
public import MathlibExt.NumberTheory.BinomidIndexBinomidUpperAverageEqISup
public import MathlibExt.NumberTheory.BinomidIndexApplyPeriodEqApplyZero
public import MathlibExt.NumberTheory.BinomidIndexBinomidShiftImageInterEqZero

namespace MetaMathlibExt

@[expose] public section

/-- **Monotone finite binomid indices extend periodically.** Let $m \ge 1$ and let
$e_1 \le e_2 \le \cdots \le e_m$ be nonnegative integers. Then the periodic sequence
$(e_1, \dots, e_m, e_1, \dots, e_m, \dots)$ is the lex-minimal extension of $(e_1, \dots, e_m)$.

A non-decreasing finite sequence is automatically a finite binomid index.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 3
(`integers-2024-A53-prop-3`). -/
public theorem_wanted isLexMinimalExtensionOf_periodic_of_monotoneOn {m : ℕ}
    (hm : 0 < m) {e : ℕ → ℕ} (he : MonotoneOn e (Set.Iio m)) :
    IsLexMinimalExtensionOf (fun i => e (i % m)) m

/-- **Periodic binomid indices are lex-minimal extensions.** If an infinite binomid index
$e = (e_1, e_2, \dots)$ is periodic, that is, there is $p \ge 1$ with $e_{i+p} = e_i$ for all
$i$, then $e$ is a lex-minimal extension: it is the lex-minimal extension of
$(e_1, \dots, e_m)$ for some $m \ge 0$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 5
(`integers-2024-A53-prop-5`). -/
public theorem_wanted isLexMinimalExtension_of_periodic {η : ℕ → ℕ}
    (hη : IsBinomidIndex η) {p : ℕ} (hp : 0 < p) (hper : ∀ i, η (i + p) = η i) :
    IsLexMinimalExtension η

/-- **Primes divide all inner Fibonomial coefficients of infinitely many rows.** Let $F_n$ be
the Fibonacci numbers and $F_n! = F_1 F_2 \cdots F_n$ the Fibonacci factorial. For every prime
$p$ there are infinitely many natural numbers $n$ such that for every $k$ with $1 \le k < n$ the
Fibonomial coefficient $F_n! / (F_k! \, F_{n-k}!)$ is an integer multiple of $p$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 4
(`integers-2024-A53-cor-4`). -/
public theorem_wanted infinite_setOf_prime_dvd_fibonomial {p : ℕ} (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → ∃ z : ℤ,
      fibonacciFactorial n / (fibonacciFactorial k * fibonacciFactorial (n - k))
        = (p : ℚ) * z}.Infinite

/-- **The lex-minimal extension is computed greedily.** Let $m \ge 1$ and let
$f = (f_1, f_2, \dots)$ be a sequence of nonnegative integers whose first $m$ entries form a
finite binomid index, that is, $\sum_{i=n-k+1}^{n} f_i \ge \sum_{i=1}^{k} f_i$ for all
$1 \le k \le n \le m$. Suppose that for every $n > m$ the entry $f_n$ equals the maximum,
over $1 \le k < n$, of the integers $\sum_{i=1}^{k} f_i - \sum_{i=n-k+1}^{n-1} f_i$. Then $f$
is the lex-minimal extension of $(f_1, \dots, f_m)$.

The differences are taken in the integers and may be negative; the condition says that
$f_n + \sum_{i=n-k+1}^{n-1} f_i \ge \sum_{i=1}^{k} f_i$ for every $1 \le k < n$, with equality
for some such $k$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 2
(`integers-2024-A53-prop-2`). -/
public theorem_wanted isLexMinimalExtensionOf_of_greedy {m : ℕ} (hm : 0 < m) {f : ℕ → ℕ}
    (hpre : ∀ k n : ℕ, k ≤ n → n ≤ m →
      ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.Ico (n - k) n, f i)
    (hle : ∀ j, m ≤ j → ∀ k, 1 ≤ k → k ≤ j →
      ∑ i ∈ Finset.range k, f i ≤ f j + ∑ i ∈ Finset.Ico (j + 1 - k) j, f i)
    (hex : ∀ j, m ≤ j → ∃ k, 1 ≤ k ∧ k ≤ j ∧
      ∑ i ∈ Finset.range k, f i = f j + ∑ i ∈ Finset.Ico (j + 1 - k) j, f i) :
    IsLexMinimalExtensionOf f m

/-- **Lex-minimal extensions have a nomid coefficient equal to one.** Let $m \ge 1$, let
$\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of its first $m$ entries, and let $p$ be a
prime. Write $f_i = p^{e_i}$ for $i \ge 1$ and, for $1 \le k \le n$, let
$[n, k]_f = \frac{f_n f_{n-1} \cdots f_{n-k+1}}{f_k f_{k-1} \cdots f_1}$ be the $f$-nomid
coefficient, the generalized binomial coefficient of $f$. Then for every $n > m$ there is some $k$
with $1 \le k < n$ and $[n, k]_f = 1$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 2
(`integers-2024-A53-cor-2`). -/
public theorem_wanted IsLexMinimalExtensionOf.exists_nomid_eq_one {η : ℕ → ℕ} {m : ℕ}
    (hm : 0 < m) (hη : IsLexMinimalExtensionOf η m) {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : m < n) :
    ∃ k, 1 ≤ k ∧ k < n ∧
      generalizedBinomialCoefficient (fun i => p ^ η (i - 1)) k (n - k) = 1

/-- **Lex-minimal extensions satisfy the Average Condition.** Every lex-minimal extension
satisfies the Average Condition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3
(`integers-2024-A53-lem-3`). -/
public theorem_wanted IsLexMinimalExtension.binomidAverageCondition {η : ℕ → ℕ}
    (hη : IsLexMinimalExtension η) : BinomidAverageCondition η

/-- **The Average Condition gives eventually periodic lex-minimal extensions.** If an
infinite binomid index $e = (e_1, e_2, \dots)$ satisfies the Average Condition, then $e$ is
a lex-minimal extension, that is, the lex-minimal extension of $(e_1, \dots, e_m)$ for some
$m \ge 0$, and $e$ is eventually periodic: there are $N$ and $p \ge 1$ such that
$e_{n+p} = e_n$ for all $n \ge N$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Theorem 1
(`integers-2024-A53-thm-1`). -/
public theorem_wanted IsBinomidIndex.isLexMinimalExtension_and_eventually_periodic
    {η : ℕ → ℕ} (hη : IsBinomidIndex η) (hac : BinomidAverageCondition η) :
    IsLexMinimalExtension η ∧ ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → η (n + p) = η n

end

end MetaMathlibExt
