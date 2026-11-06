/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.AlmostPrime
public import Mathlib.Data.Nat.Nth
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptotic
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted

/-!
# Almost primes of almost prime index

Statements from Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime
Index*, INTEGERS 24 (2024), Article A99.

A `k`-almost prime is a positive integer with exactly `k` prime factors counted with
multiplicity (Mathlib's `Nat.IsAlmostPrime k`). `N_{j,k}` is the set of `j`-almost primes whose
index in the increasing enumeration of the `j`-almost primes is a `k`-almost prime, and
`N_{k_1 k_2 ⋯ k_m}` iterates this: its elements are the `k_1`-almost primes whose index is in
`N_{k_2 ⋯ k_m}`. Indices are `1`-based as in the paper, so the `i`th `k`-almost prime is
`Nat.nth (Nat.IsAlmostPrime k) (i - 1)`, and the `n`th prime `p_n` is `Nat.nth Nat.Prime (n - 1)`.

The counting function `N_{k_1 ⋯ k_m}(x)` is the number of members of `N_{k_1 ⋯ k_m}` that are at
most `x`, written `Set.ncard {n | n ∈ almostPrimeIndexSet k_1 [k_2, …, k_m] ∧ (n : ℝ) ≤ x}`;
the count `N_k(x)` of `k`-almost primes up to `x` is the existing
`MetaMathlibExt.almostPrimeCounting k ⌊x⌋₊` (so `N_2(x)` counts the semiprimes). As in the
paper, `log_2 x = log log x` and `log_3 x = log log log x`, while `log^n x` is a power. The
Meissel–Mertens constant
`β = lim_{x → ∞} (∑_{p ≤ x} 1/p - log log x)` is the existing
`MetaMathlibExt.meisselMertensConstant`.
-/

namespace MetaMathlibExt

open Filter Asymptotics Topology

@[expose] public section

/-- **Almost primes of almost prime index.** For natural numbers $k_1, \dots, k_m$ with $m \ge 1$,
the set $N_{k_1 \cdots k_m}$ of natural numbers is defined by recursion on $m$: $N_{k_1}$ is the
set of $k_1$-almost primes (the $n \ne 0$ with exactly $k_1$ prime factors counted with
multiplicity), and for $m \ge 2$, $N_{k_1 \cdots k_m}$ is the set of the $i$th $k_1$-almost
primes, in increasing order and counted from $1$, for $i \ge 1$ in $N_{k_2 \cdots k_m}$. When
there are fewer than $i$ $k_1$-almost primes (only for $k_1 = 0$, where $1$ is the only one),
the $i$th one is taken to be $0$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definitions of `N_k`, `N_{j,k}`, and
`N_{k_1 ⋯ k_m}`). -/
public def almostPrimeIndexSet (k : ℕ) : List ℕ → Set ℕ
  | [] => {n | Nat.IsAlmostPrime k n}
  | j :: L => {n | ∃ i ∈ almostPrimeIndexSet j L, 1 ≤ i ∧ n = Nat.nth (Nat.IsAlmostPrime k) (i - 1)}

/-- **Almost prime index sets with one index.** For every natural number $k$, the almost prime
index set $N_k$ with the single index $k$ is the set of $k$-almost primes, the natural numbers
$n \ne 0$ with exactly $k$ prime factors counted with multiplicity.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definition of `N_k`). -/
public theorem almostPrimeIndexSet_nil (k : ℕ) :
    almostPrimeIndexSet k [] = {n | Nat.IsAlmostPrime k n} := rfl

/-- **Membership in an almost prime index set.** For natural numbers $k$, $j$, $n$ and
$\ell_1, \dots, \ell_r$ (with $r \ge 0$), $n$ lies in the almost prime index set
$N_{k j \ell_1 \cdots \ell_r}$ if and only if there is an $i \ge 1$ in $N_{j \ell_1 \cdots \ell_r}$
such that $n$ is the $i$th $k$-almost prime in increasing order, counted from $1$ (taken to be $0$
if there are fewer than $i$ of them).

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Section 1 (definition of `N_{k_1 ⋯ k_m}`). -/
public theorem mem_almostPrimeIndexSet_cons (k j : ℕ) (L : List ℕ) (n : ℕ) :
    n ∈ almostPrimeIndexSet k (j :: L) ↔
      ∃ i ∈ almostPrimeIndexSet j L, 1 ≤ i ∧ n = Nat.nth (Nat.IsAlmostPrime k) (i - 1) :=
  Iff.rfl

/-- **Dusart's bounds for the $n$th prime.** For $n \ge 1$ let $p_n$ denote the $n$th prime, so
that $p_1 = 2$, and let $\log$ be the natural logarithm. For every natural number $n \ge 2$,
$$
p_n \ge n (\log n + \log \log n - 1)
$$
and
$$
p_n \ge n \left( \log n + \log \log n - 1 + \frac{\log \log n - 2.25}{\log n} \right),
$$
and for every natural number $n \ge 39017$,
$$
p_n \le n (\log n + \log \log n - 0.9484).
$$

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 4 (quoting Dusart) (`integers-2024-A99-lem-4`). -/
public theorem_wanted nth_prime_dusart_bounds :
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ) * (Real.log n + Real.log (Real.log n) - 1) ≤ Nat.nth Nat.Prime (n - 1)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ) * (Real.log n + Real.log (Real.log n) - 1 +
        (Real.log (Real.log n) - 2.25) / Real.log n) ≤ Nat.nth Nat.Prime (n - 1)) ∧
    (∀ n : ℕ, 39017 ≤ n →
      (Nat.nth Nat.Prime (n - 1) : ℝ) ≤ n * (Real.log n + Real.log (Real.log n) - 0.9484))

/-- **Convergence of reciprocal sums over almost primes of almost prime index.** A $k$-almost
prime is a positive integer with exactly $k$ prime factors counted with multiplicity. For positive
integers $k_1, \dots, k_m$ let $N_{k_1}$ be the set of $k_1$-almost primes and, for $m \ge 2$, let
$N_{k_1 k_2 \cdots k_m}$ be the set of $k_1$-almost primes whose index in the increasing
enumeration of the $k_1$-almost primes (starting at $1$) lies in $N_{k_2 \cdots k_m}$. Then for
every $m \ge 2$ and all positive integers $k_1, \dots, k_m$ the series
$\sum_{n \in N_{k_1 k_2 \cdots k_m}} 1/n$ converges.

In particular (the case $m = 2$), for all positive integers $j$ and $k$ the sum of the reciprocals
of the $j$-almost primes of $k$-almost prime index converges.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 5 (`integers-2024-A99-thm-5`). -/
public theorem_wanted summable_inv_almostPrimeIndexSet {k : ℕ} {L : List ℕ} (hk : 1 ≤ k)
    (hL : L ≠ []) (hpos : ∀ j ∈ L, 1 ≤ j) :
    Summable fun n : almostPrimeIndexSet k L => (1 : ℝ) / n

/-- **Reciprocal sum of the primes of semiprime index.** Let $N_{1,2}$ be the set of primes $p_i$
(indexed from $p_1 = 2$) whose index $i$ is a semiprime, that is, a product of two not
necessarily distinct primes. Then $0.9910 < \sum_{n \in N_{1,2}} 1/n < 0.9915$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 6 (`integers-2024-A99-thm-6`). -/
public theorem_wanted tsum_inv_primes_of_semiprime_index_bounds :
    0.9910 < ∑' n : almostPrimeIndexSet 1 [2], (1 : ℝ) / n ∧
      ∑' n : almostPrimeIndexSet 1 [2], (1 : ℝ) / n < 0.9915

/-- **Crişan–Erban expansion of the semiprime counting function.** A semiprime is a product of
exactly two primes counted with multiplicity; for real $x$ let $N_2(x)$ be the number of semiprimes
at most $x$. Let $\beta$ be the Meissel–Mertens constant, $\gamma$ the Euler–Mascheroni constant
and $\log$ the natural logarithm. There are real constants $c_0, c_1, c_2, \dots$ with
$c_0 = \beta$ and
$$
c_1 = \beta - 1 - \gamma - \sum_{p} \frac{\log p}{p (p - 1)},
$$
the sum running over all primes $p$, such that for every natural number $N$, as $x \to \infty$,
$$
N_2(x) = \frac{x}{\log x} \sum_{n=0}^{N-1} \frac{n! \, (\log \log x + c_n)}{\log^n x} +
O_N\left( \frac{x \log \log x}{\log^{N+1} x} \right).
$$

The paper calls the $c_n$ explicit but displays only $c_0$ and $c_1$; the remaining constants are
only asserted to exist.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 1 (quoting Crişan and Erban) (`integers-2024-A99-lem-1`). -/
public theorem_wanted semiprime_count_asymptotic_expansion :
    ∃ c : ℕ → ℝ, c 0 = meisselMertensConstant ∧
      c 1 = meisselMertensConstant - 1 - Real.eulerMascheroniConstant -
        ∑' p : Nat.Primes, Real.log (p : ℕ) / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1)) ∧
      ∀ N : ℕ, (fun x : ℝ => (almostPrimeCounting 2 ⌊x⌋₊ : ℝ) -
          x / Real.log x * ∑ n ∈ Finset.range N,
            (n.factorial : ℝ) * (Real.log (Real.log x) + c n) / Real.log x ^ n) =O[atTop]
        fun x => x * Real.log (Real.log x) / Real.log x ^ (N + 1)

/-- **Explicit estimate for the reciprocal sum of the semiprimes.** A semiprime is a product of
exactly two primes counted with multiplicity; for real $x$ let $S(x)$ be the sum of $1/n$ over the
semiprimes $n \le x$. Let $\beta$ be the Meissel–Mertens constant, $\gamma$ the Euler–Mascheroni
constant and $\log$ the natural logarithm, and put
$$
P(2) = \sum_{p} \frac{1}{p^2}, \qquad \zeta(2) = \frac{\pi^2}{6}, \qquad
\alpha_1 = \gamma + \sum_{p} \frac{\log p}{p (p - 1)},
$$
the sums running over all primes $p$. Then for every real $x > 1$ the error
$$
E(x) = S(x) - \frac{(\log \log x + \beta)^2}{2} - \frac{P(2) - \zeta(2)}{2} -
\frac{\alpha_1}{\log x}
$$
satisfies $|E(x)| < (\log x)^{-3/2}$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 2 (quoting Bayless et al.) (`integers-2024-A99-lem-2`). -/
public theorem_wanted semiprime_reciprocal_sum_explicit_estimate {x : ℝ} (hx : 1 < x) :
    |(∑' n : {n : ℕ // Nat.IsAlmostPrime 2 n ∧ (n : ℝ) ≤ x}, (1 : ℝ) / (n : ℕ)) -
      ((Real.log (Real.log x) + meisselMertensConstant) ^ 2 / 2 +
        ((∑' p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) - Real.pi ^ 2 / 6) / 2 +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, Real.log (p : ℕ) / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1))) /
          Real.log x)| <
      Real.log x ^ (-(3 / 2 : ℝ))

/-- **Erdős–Sárközy bound for almost primes.** There is a real constant $C$ such that for every
integer $k \ge 1$ and every real $t \ge 1$, the number $\pi_{k+1}(t)$ of integers $n$ with
$1 \le n \le t$ that have exactly $k + 1$ prime factors, counted with multiplicity, satisfies
$\pi_{k+1}(t) \le C \cdot \frac{k^4}{2^k} \, t \log t$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 3 (quoting Erdős and Sárközy) (`integers-2024-A99-lem-3`). -/
public theorem_wanted almostPrime_count_le_erdos_sarkozy :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 1 ≤ t →
      (almostPrimeCounting (k + 1) ⌊t⌋₊ : ℝ) ≤
        C * ((k : ℝ) ^ 4 / 2 ^ k) * t * Real.log t

/-- **Logarithmic expansions of the prime counting function.** Let $\pi(x)$ be the number of
primes $p \le x$. As $x \to \infty$,

$$
\log \pi(x) = \log x - \log \log x + \frac{1}{\log x} + \frac{3}{2 (\log x)^2} +
O\left(\frac{1}{(\log x)^3}\right),
$$

$$
\log \log \pi(x) = \log \log x - \frac{\log \log x}{\log x} -
\frac{(\log \log x)^2}{2 (\log x)^2} + \frac{1}{(\log x)^2} +
O\left(\frac{(\log \log x)^3}{(\log x)^3}\right),
$$

and

$$
\frac{1}{\log \pi(x)} - \frac{1}{\log x}\left(1 + \frac{\log \log x}{\log x} +
\frac{(\log \log x)^2 - 1}{(\log x)^2} + \frac{(\log \log x)^3}{(\log x)^3}\right) =
O\left(\frac{\log \log x}{(\log x)^4}\right).
$$

The last expansion is the paper's form, whose error term $O(\log \log x / (\log x)^3)$ sits
inside the parentheses, multiplied out by the factor $1/\log x$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 5 (`integers-2024-A99-lem-5`). -/
public theorem_wanted log_primeCounting_asymptotics :
    ((fun x : ℝ => Real.log (Nat.primeCounting ⌊x⌋₊) -
        (Real.log x - Real.log (Real.log x) + 1 / Real.log x + 3 / (2 * Real.log x ^ 2)))
      =O[atTop] fun x => 1 / Real.log x ^ 3) ∧
    ((fun x : ℝ => Real.log (Real.log (Nat.primeCounting ⌊x⌋₊)) -
        (Real.log (Real.log x) - Real.log (Real.log x) / Real.log x -
          Real.log (Real.log x) ^ 2 / (2 * Real.log x ^ 2) + 1 / Real.log x ^ 2))
      =O[atTop] fun x => Real.log (Real.log x) ^ 3 / Real.log x ^ 3) ∧
    ((fun x : ℝ => 1 / Real.log (Nat.primeCounting ⌊x⌋₊) -
        1 / Real.log x * (1 + Real.log (Real.log x) / Real.log x +
          (Real.log (Real.log x) ^ 2 - 1) / Real.log x ^ 2 +
          Real.log (Real.log x) ^ 3 / Real.log x ^ 3))
      =O[atTop] fun x => Real.log (Real.log x) / Real.log x ^ 4)

/-- **Expansion of the reciprocal logarithm of the semiprime count.** Let $\pi_2(x)$ be the
number of integers $n$ with $1 \le n \le x$ that have exactly two prime factors counted with
multiplicity, and let $\beta$ be the Meissel–Mertens constant. Then, as $x \to \infty$,

$$
\frac{1}{\log \pi_2(x)} - \frac{1}{\log x}\left(1 + \frac{\log \log x}{\log x} -
\frac{\log \log \log x}{\log x} - \frac{\beta}{\log x \, \log \log x}\right) =
O\left(\frac{1}{(\log x)^2 (\log \log x)^2}\right).
$$

This is the paper's expansion, whose error term $O(1/(\log x \, (\log \log x)^2))$ sits inside
the parentheses, multiplied out by the factor $1/\log x$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 6 (`integers-2024-A99-lem-6`). -/
public theorem_wanted inv_log_semiprime_count_asymptotic :
    (fun x : ℝ => 1 / Real.log (almostPrimeCounting 2 ⌊x⌋₊) -
        1 / Real.log x * (1 + Real.log (Real.log x) / Real.log x -
          Real.log (Real.log (Real.log x)) / Real.log x -
          meisselMertensConstant / (Real.log x * Real.log (Real.log x))))
      =O[atTop] fun x => 1 / (Real.log x ^ 2 * Real.log (Real.log x) ^ 2)

/-- **Counting primes of semiprime index.** A semiprime is a product of exactly two primes counted
with multiplicity. Let $p_i$ denote the $i$th prime ($p_1 = 2$), and for real $x$ let $N_{1,2}(x)$
be the number of primes $p_i \le x$ whose index $i$ is a semiprime. Let $\beta$ be the
Meissel–Mertens constant, $\gamma$ the Euler–Mascheroni constant, $\log$ the natural logarithm, and
$$
c_1 = \beta - 1 - \gamma - \sum_{p} \frac{\log p}{p (p - 1)},
$$
the sum running over all primes $p$. Then, as $x \to \infty$,
$$
N_{1,2}(x) = \frac{x}{\log^2 x} \left( \log \log x + \beta +
\frac{(\log \log x + \beta)(\log \log x + 1) + c_1}{\log x} \right) +
O\left( \frac{x (\log \log x)^3}{\log^4 x} \right).
$$

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 1 (`integers-2024-A99-thm-1`). -/
public theorem_wanted primes_of_semiprime_index_count_asymptotic :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 1 [2] ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ 2 * (Real.log (Real.log x) + meisselMertensConstant +
          ((Real.log (Real.log x) + meisselMertensConstant) * (Real.log (Real.log x) + 1) +
            (meisselMertensConstant - 1 - Real.eulerMascheroniConstant -
              ∑' p : Nat.Primes, Real.log (p : ℕ) / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1)))) /
            Real.log x))
      =O[atTop] fun x => x * Real.log (Real.log x) ^ 3 / Real.log x ^ 4

/-- **Counting semiprimes of prime index.** A semiprime is a product of exactly two primes counted
with multiplicity. Let $s_i$ denote the $i$th semiprime ($s_1 = 4$), and for real $x$ let
$N_{2,1}(x)$ be the number of semiprimes $s_i \le x$ whose index $i$ is prime. Let $\beta$ be the
Meissel–Mertens constant and $\log$ the natural logarithm. Then, as $x \to \infty$,
$$
N_{2,1}(x) = \frac{x}{\log^2 x} \left( \log \log x + \beta +
\frac{\log \log x \, (\log \log x - \log \log \log x)}{\log x} \right) +
O\left( \frac{x \log \log x}{\log^3 x} \right).
$$

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 2 (`integers-2024-A99-thm-2`). -/
public theorem_wanted semiprimes_of_prime_index_count_asymptotic :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 2 [1] ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ 2 * (Real.log (Real.log x) + meisselMertensConstant +
          Real.log (Real.log x) * (Real.log (Real.log x) - Real.log (Real.log (Real.log x))) /
            Real.log x))
      =O[atTop] fun x => x * Real.log (Real.log x) / Real.log x ^ 3

/-- **Primes of semiprime index eventually outnumber semiprimes of prime index.** A semiprime is
a product of exactly two primes counted with multiplicity. Let $p_i$ denote the $i$th prime
($p_1 = 2$) and $s_i$ the $i$th semiprime ($s_1 = 4$). For real $x$ let $N_{1,2}(x)$ be the number
of primes $p_i \le x$ whose index $i$ is a semiprime, and $N_{2,1}(x)$ the number of semiprimes
$s_i \le x$ whose index $i$ is prime. Then $N_{2,1}(x) < N_{1,2}(x)$ for all sufficiently large
$x$, and, with $\log$ the natural logarithm, as $x \to \infty$
$$
N_{1,2}(x) - N_{2,1}(x) = \frac{x \log \log x \, \log \log \log x}{\log^3 x} +
O\left( \frac{x \log \log x}{\log^3 x} \right).
$$

This is the form
$\frac{x \log \log x \, \log \log \log x}{\log^3 x} (1 + O(1 / \log \log \log x))$ with the main
factor multiplied out.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Corollary 1 (`integers-2024-A99-cor-1`). -/
public theorem_wanted primes_of_semiprime_index_count_sub_semiprimes_of_prime_index :
    (∀ᶠ x : ℝ in atTop,
      Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 2 [1] ∧ (n : ℝ) ≤ x} <
        Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 1 [2] ∧ (n : ℝ) ≤ x}) ∧
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 1 [2] ∧ (n : ℝ) ≤ x} : ℝ) -
        Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet 2 [1] ∧ (n : ℝ) ≤ x} -
        x * Real.log (Real.log x) * Real.log (Real.log (Real.log x)) / Real.log x ^ 3)
      =O[atTop] fun x => x * Real.log (Real.log x) / Real.log x ^ 3

/-- **Counting almost primes of almost prime index.** Let $j, k \ge 1$ be integers and, for real
$x$, let $N_{jk}(x)$ be the number of $j$-almost primes $n \le x$ whose index in the increasing
enumeration of the $j$-almost primes, counted from $1$, is a $k$-almost prime. Writing
$M(x) = \frac{x \, (\log \log x)^{j+k-2}}{(\log x)^2 \, (j-1)! \, (k-1)!}$, we have
$N_{jk}(x) - M(x) = O(M(x) / \log \log x)$ as $x \to \infty$.

The paper's clause "the same estimate holds for $N_{kj}$" is the instance with $j$ and $k$
swapped, since the main term is symmetric.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 3 (`integers-2024-A99-thm-3`). -/
public theorem_wanted almostPrimeIndexSet_pair_count_asymptotic {j k : ℕ} (hj : 1 ≤ j)
    (hk : 1 ≤ k) :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet j [k] ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ 2 * Real.log (Real.log x) ^ (j + k - 2) /
          ((j - 1).factorial * (k - 1).factorial))
      =O[atTop] fun x => x / Real.log x ^ 2 * Real.log (Real.log x) ^ (j + k - 2) /
          ((j - 1).factorial * (k - 1).factorial) / Real.log (Real.log x)

/-- **Counting almost primes of iterated almost prime index.** Let $m \ge 1$, let
$k_1, \dots, k_m$ be positive integers, let $N_{k_1 \cdots k_m}$ be the almost prime index set
(for $m = 1$ the $k_1$-almost primes, and for $m \ge 2$ the $k_1$-almost primes whose index in
increasing order, counted from $1$, lies in $N_{k_2 \cdots k_m}$), and for real $x$ let
$N_{k_1 \cdots k_m}(x)$ be the number of its elements $n \le x$. Writing
$M(x) = \frac{x}{(\log x)^m} \prod_{i=1}^m \frac{(\log \log x)^{k_i - 1}}{(k_i - 1)!}$, we have
$N_{k_1 \cdots k_m}(x) - M(x) = O(M(x) / \log \log x)$ as $x \to \infty$.

The paper's displayed exponent $k_1 + \cdots + k_{m-1} k_m - m$ is a typo for
$k_1 + \cdots + k_{m-1} + k_m - m$, as its equivalent product form shows.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 4 (`integers-2024-A99-thm-4`). -/
public theorem_wanted almostPrimeIndexSet_count_asymptotic {k : ℕ} {ks : List ℕ}
    (hpos : ∀ i ∈ k :: ks, 1 ≤ i) :
    (fun x : ℝ => (Set.ncard {n : ℕ | n ∈ almostPrimeIndexSet k ks ∧ (n : ℝ) ≤ x} : ℝ) -
        x / Real.log x ^ (ks.length + 1) *
          ((k :: ks).map fun i => Real.log (Real.log x) ^ (i - 1) / (i - 1).factorial).prod)
      =O[atTop] fun x => x / Real.log x ^ (ks.length + 1) *
          ((k :: ks).map fun i => Real.log (Real.log x) ^ (i - 1) / (i - 1).factorial).prod /
          Real.log (Real.log x)

/-- **Size of the nth almost prime of almost prime index.** Let $j, k \ge 1$ be integers and, for
$n \ge 1$, let $p_{j,k,n}$ be the $n$th element, in increasing order, of the set $N_{jk}$ of
$j$-almost primes whose index in the increasing enumeration of the $j$-almost primes, counted
from $1$, is a $k$-almost prime. Writing
$P(n) = \frac{n (\log n)^2 \, (j-1)! \, (k-1)!}{(\log \log n)^{j+k-2}}$, we have
$p_{j,k,n} - P(n) = O(P(n) / \log \log n)$ as $n \to \infty$ through the integers.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Corollary 2 (`integers-2024-A99-cor-2`). -/
public theorem_wanted nth_almostPrimeIndexSet_pair_asymptotic {j k : ℕ} (hj : 1 ≤ j)
    (hk : 1 ≤ k) :
    (fun n : ℕ => (Nat.nth (· ∈ almostPrimeIndexSet j [k]) (n - 1) : ℝ) -
        n * Real.log n ^ 2 * ((j - 1).factorial * (k - 1).factorial) /
          Real.log (Real.log n) ^ (j + k - 2))
      =O[atTop] fun n : ℕ => n * Real.log n ^ 2 * ((j - 1).factorial * (k - 1).factorial) /
          Real.log (Real.log n) ^ (j + k - 2) / Real.log (Real.log n)

/-- **Size of the nth element of an iterated almost prime index set.** Let $m \ge 1$, let
$k_1, \dots, k_m$ be positive integers, and for $n \ge 1$ let $p_{k_1, \dots, k_m, n}$ be the
$n$th element, in increasing order, of the almost prime index set $N_{k_1 \cdots k_m}$. Writing
$P(n) = n (\log n)^m \prod_{i=1}^m \frac{(k_i - 1)!}{(\log \log n)^{k_i - 1}}$, we have
$p_{k_1, \dots, k_m, n} - P(n) = O(P(n) / \log \log n)$ as $n \to \infty$ through the integers.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Corollary 3 (`integers-2024-A99-cor-3`). -/
public theorem_wanted nth_almostPrimeIndexSet_asymptotic {k : ℕ} {ks : List ℕ}
    (hpos : ∀ i ∈ k :: ks, 1 ≤ i) :
    (fun n : ℕ => (Nat.nth (· ∈ almostPrimeIndexSet k ks) (n - 1) : ℝ) -
        n * Real.log n ^ (ks.length + 1) *
          ((k :: ks).map fun i => ((i - 1).factorial : ℝ) / Real.log (Real.log n) ^ (i - 1)).prod)
      =O[atTop] fun n : ℕ => n * Real.log n ^ (ks.length + 1) *
          ((k :: ks).map fun i => ((i - 1).factorial : ℝ) / Real.log (Real.log n) ^ (i - 1)).prod /
          Real.log (Real.log n)

/-- **Reciprocal sum of the primes of $k$-almost prime index.** For $k \ge 0$ let $N_{1k}$ be
the set of primes $p_i$ (indexed from $p_1 = 2$) whose index $i$ is a $k$-almost prime, that is,
has exactly $k$ prime factors counted with multiplicity. Then
$\sum_{n \in N_{1k}} 1/n = 1 + O(e^{-k/2})$ as $k \to \infty$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 7 (`integers-2024-A99-thm-7`). -/
public theorem_wanted tsum_inv_primes_of_almostPrime_index_sub_one_isBigO :
    (fun k : ℕ => (∑' n : almostPrimeIndexSet 1 [k], (1 : ℝ) / n) - 1)
      =O[atTop] fun k : ℕ => Real.exp (-(k : ℝ) / 2)

/-- **Lower bound for reciprocal sums over almost primes of almost prime index.** A $k$-almost
prime is a positive integer with exactly $k$ prime factors counted with multiplicity. For positive
integers $j$ and $k$ let $N_{jk}$ be the set of $j$-almost primes whose index in the increasing
enumeration of the $j$-almost primes (starting at $1$) is a $k$-almost prime. Fix an integer
$j \ge 1$. There is a real constant $c > 0$ such that
$$
\sum_{n \in N_{jk}} \frac{1}{n} \ge c \, k^{j-1}
$$
for all sufficiently large $k$. Moreover, if $j \ge 2$, then $\sum_{n \in N_{jk}} 1/n \to \infty$
as $k \to \infty$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 8 (`integers-2024-A99-thm-8`). -/
public theorem_wanted tsum_inv_almostPrimeIndexSet_pair_lower_bound {j : ℕ} (hj : 1 ≤ j) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      c * (k : ℝ) ^ (j - 1) ≤ ∑' n : almostPrimeIndexSet j [k], (1 : ℝ) / n) ∧
    (2 ≤ j → Tendsto (fun k : ℕ => ∑' n : almostPrimeIndexSet j [k], (1 : ℝ) / n) atTop atTop)

/-- **Exponential decay of reciprocal sums over triple almost prime index sets.** A $k$-almost
prime is a positive integer with exactly $k$ prime factors counted with multiplicity. For positive
integers $a$ and $b$ let $N_{ab}$ be the set of $a$-almost primes whose index in the increasing
enumeration of the $a$-almost primes (starting at $1$) is a $b$-almost prime, and for positive
integers $k_1, k_2, k$ let $N_{k_1 k_2 k}$ be the set of $k_1$-almost primes whose index in the
increasing enumeration of the $k_1$-almost primes lies in $N_{k_2 k}$. Fix positive integers $k_1$
and $k_2$. Then, as $k \to \infty$,
$$
\sum_{n \in N_{k_1 k_2 k}} \frac{1}{n} = O\left( e^{-k/2} \right).
$$

This is the case $m = 2$ of the paper's bound $\ll (e^{k/2})^{-(m-1)}$ for the reciprocal sum of
$N_{k_1 \cdots k_m k}$, the only case its proof supports. For $m = 3$ and $k_1 = k_2 = k_3 = 1$,
with $p_n$ the $n$th prime, the single term $1/p_{p_{p_{2^k}}}$ is $\gg 2^{-k} k^{-3}$ because
$p_n < n (\log n + \log \log n)$ for $n \ge 6$, and $e^{k} 2^{-k} k^{-3} \to \infty$, so the
printed bound fails for $m = 3$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 9, case `m = 2` (`integers-2024-A99-thm-9`). -/
public theorem_wanted tsum_inv_almostPrimeIndexSet_triple_isBigO {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁)
    (hk₂ : 1 ≤ k₂) :
    (fun k : ℕ => ∑' n : almostPrimeIndexSet k₁ [k₂, k], (1 : ℝ) / n)
      =O[atTop] fun k : ℕ => Real.exp (-(k : ℝ) / 2)

/-- **Reciprocal sums over iterated almost prime index sets tend to zero.** A $k$-almost prime is
a positive integer with exactly $k$ prime factors counted with multiplicity. For positive integers
$k_1, \dots, k_m$ let $N_{k_1}$ be the set of $k_1$-almost primes and, for $m \ge 2$, let
$N_{k_1 k_2 \cdots k_m}$ be the set of $k_1$-almost primes whose index in the increasing
enumeration of the $k_1$-almost primes (starting at $1$) lies in $N_{k_2 \cdots k_m}$. Fix
$m \ge 2$ and positive integers $k_1, \dots, k_m$. Then
$$
\lim_{k \to \infty} \sum_{n \in N_{k_1 \cdots k_m k}} \frac{1}{n} = 0.
$$

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Theorem 9, "in particular" clause (`integers-2024-A99-thm-9`). -/
public theorem_wanted tendsto_tsum_inv_almostPrimeIndexSet_append_zero {k : ℕ} {ks : List ℕ}
    (hks : ks ≠ []) (hpos : ∀ i ∈ k :: ks, 1 ≤ i) :
    Tendsto (fun k' : ℕ => ∑' n : almostPrimeIndexSet k (ks ++ [k']), (1 : ℝ) / n) atTop (𝓝 0)

end

end MetaMathlibExt
