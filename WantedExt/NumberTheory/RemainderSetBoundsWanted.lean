/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.PierceExpansion

/-!
# Bounds for sets of remainders (statements)

Statement-only targets from Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of
Remainders*, Journal of Integer Sequences 29 (2026), Article 26.1.4.

`S(n) = {n mod k : 1 ≤ k ≤ ⌊n/2⌋}` and `s(n) = |S(n)|` (OEIS A283190). The paper's
structural lemmas, its `O(log log n)` drop bound, and its iterated-set bounds are proved in
`FormalizedPapers/NumberTheory/BaraskarVukusic2026` (there `S 1 n` is this `remainderSet n`);
`WantedExt` may not import `FormalizedPapers`, so the set is restated here. This file states
the results that are not proved there: the asymptotic `s(n) = cn + O(n/(log n log log n))`,
unbounded drops, the three auxiliary analytic lemmas, and Lemma 19 (iterated remainder sets
`S_j(n)` versus the Pierce length `P(n)`, in corrected form).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Remainder set.** For a natural number $n$, the remainder set is
$S(n) = \{\, n \bmod k : 1 \le k \le \lfloor n/2 \rfloor \,\}$, the set of remainders of $n$
modulo the integers from $1$ to $\lfloor n/2 \rfloor$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `S(n)`). -/
public def remainderSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n / 2)).image (n % ·)

/-- **Remainder count.** For a natural number $n$, $s(n)$ is the number of elements of the
remainder set $S(n)$, that is, the number of distinct values of $n \bmod k$ for
$1 \le k \le \lfloor n/2 \rfloor$ (OEIS A283190).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `s(n)`). -/
public def remainderCount (n : ℕ) : ℕ :=
  (remainderSet n).card

/-- **The remainder count of 11.** The number $s(11)$ of distinct remainders $11 \bmod k$ for
$1 \le k \le 5$ equals $4$.

These remainders form the set $S(11) = \{0, 1, 2, 3\}$ (Table 1 of the paper).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Table 1. -/
public theorem remainderCount_eleven : remainderCount 11 = 4 := by decide

/-- **The remainder count of 12.** The number $s(12)$ of distinct remainders $12 \bmod k$ for
$1 \le k \le 6$ equals $2$.

This is a drop from $s(11) = 4$, the number of distinct remainders $11 \bmod k$ for
$1 \le k \le 5$ (Table 1 of the paper).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Table 1. -/
public theorem remainderCount_twelve : remainderCount 12 = 2 := by decide

/-- **The remainder-set constant.** The remainder-set constant is
$c = \sum_{p} \frac{1}{p(p+1)} \prod_{q < p} \left(1 - \frac{1}{q}\right)$, where $p$ runs
over all primes and, for each $p$, $q$ runs over the primes less than $p$.

Numerically, $c \approx 0.2296$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, equation `eq:asymp`. -/
public noncomputable def remainderConstant : ℝ :=
  ∑' p : Nat.Primes, (1 / ((p : ℝ) * ((p : ℝ) + 1))) *
    ∏ q ∈ (Finset.range p).filter Nat.Prime, (1 - 1 / (q : ℝ))

/-- **Asymptotic formula for the number of remainders.** Let $s(n)$ be the number of distinct
remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$ and let $c$ be the remainder-set
constant. Then, as $n \to \infty$ over the natural numbers,
$s(n) - cn = O\bigl(n / (\log n \cdot \log \log n)\bigr)$, and $s(n)/n \to c$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Theorem 1 (`thm:asymp`). -/
public theorem_wanted remainderCount_asymptotic :
    (fun n : ℕ => (remainderCount n : ℝ) - remainderConstant * n) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) / (Real.log n * Real.log (Real.log n))) ∧
      Filter.Tendsto (fun n : ℕ => (remainderCount n : ℝ) / n) Filter.atTop
        (nhds remainderConstant)

/-- **Unbounded drops in the number of remainders.** Let $s(n)$ be the number of distinct
remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$. For every natural number $M$
there are infinitely many $n$ with $s(n+1) + M \le s(n)$; equivalently,
$\liminf_{n \to \infty} (s(n+1) - s(n)) = -\infty$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Proposition 17 (`prop:diffs_unbounded`). -/
public theorem_wanted remainderCount_drops_unbounded (M : ℕ) :
    ∃ᶠ n in Filter.atTop, remainderCount (n + 1) + M ≤ remainderCount n

/-- **Consecutive differences of the number of remainders.** Let $s(n)$ be the number of
distinct remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$. Then
$s(n+1) \le s(n) + 1$ for every $n \ge 1$; there is a real constant $C$ with
$s(n) - C \log \log n \le s(n+1)$ for all sufficiently large $n$; and for every natural number
$M$ there are infinitely many $n$ with $s(n+1) + M \le s(n)$, that is,
$\liminf_{n \to \infty} (s(n+1) - s(n)) = -\infty$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Theorem 2 (`thm:diffs`). -/
public theorem_wanted remainderCount_consecutive_differences :
    (∀ n, 1 ≤ n → remainderCount (n + 1) ≤ remainderCount n + 1) ∧
      (∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
        (remainderCount n : ℝ) - C * Real.log (Real.log n) ≤ remainderCount (n + 1)) ∧
      ∀ M : ℕ, ∃ᶠ n in Filter.atTop, remainderCount (n + 1) + M ≤ remainderCount n

/-- **Counting integers with a given least prime factor in an interval.** Let $a$ and $t$ be
positive integers and let $p$ be a prime. Let $N$ be the number of integers $m$ with
$a + 1 \le m \le a + t$ that are divisible by $p$ and by no prime $q < p$. Then

$$\left| N - \frac{t}{p} \prod_{q < p,\ q \text{ prime}} \left(1 - \frac{1}{q}\right) \right|
\le 2^{\pi(p-1)}$$

where $\pi$ is the prime-counting function.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 6 (`lem:Dp`). -/
public theorem_wanted card_leastPrimeFactor_interval_error {a t p : ℕ} (ha : 0 < a)
    (ht : 0 < t) (hp : p.Prime) :
    |((((Finset.Icc (a + 1) (a + t)).filter
          (fun m => p ∣ m ∧ ∀ q < p, q.Prime → ¬ q ∣ m)).card : ℕ) : ℝ) -
        t * (1 / (p : ℝ)) * ∏ q ∈ (Finset.range p).filter Nat.Prime, (1 - 1 / (q : ℝ))| ≤
      2 ^ Nat.primeCounting (p - 1)

/-- **Upper bound $1.3\, n / \log n$ for the prime-counting function.** For every natural
number $n \ge 2$, the number $\pi(n)$ of primes at most $n$ satisfies
$\pi(n) \le 1.3\, n / \log n$, where $\log$ is the natural logarithm.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 7 (`lem:primecounting_ub`). -/
public theorem_wanted primeCounting_le_thirteen_tenths {n : ℕ} (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ 13 / 10 * n / Real.log n

/-- **Tail of the sum of inverse prime squares.** As the natural number $n$ tends to infinity,
the sum $\sum_{p > n,\ p \text{ prime}} 1/p^2$ of the inverse squares of the primes greater
than $n$ is $O(1/(n \log n))$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 8 (`lem:psquared_sum_est`). -/
public theorem_wanted tsum_inv_sq_primes_gt_isBigO :
    (fun n : ℕ => ∑' p : {p : ℕ // p.Prime ∧ n < p}, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2)
      =O[Filter.atTop] (fun n : ℕ => 1 / ((n : ℝ) * Real.log n))

/-- **Iterated remainder sets.** For a natural number $n$, the iterated remainder sets
$S_j(n)$, $j \ge 0$, are defined by $S_0(n) = \{1, \dots, \lfloor n/2 \rfloor\}$ and, for
$j \ge 0$, $S_{j+1}(n) = \{n \bmod k : k \in S_j(n),\ k \ne 0\}$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 2 (definition of `S_j(n)`). -/
public def iteratedRemainderSet : ℕ → ℕ → Finset ℕ
  | 0, n => Finset.Icc 1 (n / 2)
  | j + 1, n => ((iteratedRemainderSet j n).erase 0).image (n % ·)

/-- **The first iterated remainder set is the remainder set.** For every natural number $n$, the
iterated remainder set $S_1(n)$ equals the remainder set
$S(n) = \{n \bmod k : 1 \le k \le \lfloor n/2 \rfloor\}$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 2 (`S(n) = S_1(n)`). -/
public theorem iteratedRemainderSet_one (n : ℕ) : iteratedRemainderSet 1 n = remainderSet n := by
  simp [iteratedRemainderSet, remainderSet]

/-- **Iterated remainder sets of 35.** The iterated remainder sets of $35$ satisfy
$S_6(35) = \{0\}$ and $S_7(35) = \emptyset$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 2 (definition of `S_j(n)`). -/
public theorem iteratedRemainderSet_thirtyFive :
    iteratedRemainderSet 6 35 = {0} ∧ iteratedRemainderSet 7 35 = ∅ := by
  decide

/-- **Maximal Pierce length via iterated remainder sets.** Let $n \ge 3$ and $t$ be natural
numbers, let $P(n)$ be the maximal Pierce length of $n$ and let $S_j(n)$ be the iterated
remainder sets of $n$. Then the following are equivalent: $P(n) = t + 1$; $S_t(n) = \{0\}$;
$S_t(n)$ has exactly one element and $S_{t+j}(n) = \emptyset$ for every $j \ge 1$.

This corrects the index of the printed lemma, $P(n) = t \iff S_{t+1}(n) = \{0\}$, which fails
for every $n \ge 3$: for example $P(5) = 3$, $S_2(5) = \{0\}$ and $S_4(5) = \emptyset$. The
paper derives the lemma from its Lemma 18 ($r \in S_j(n)$ if and only if $a_{j+1} = r$ for some
$\lfloor n/2 \rfloor + 1 \le a \le n$, where $a_0 = a$ and $a_{i+1} = n \bmod a_i$), which
gives the index $P(n) - 1$. Lemma 18, and hence this lemma, needs $n \ge 3$: $P(2) = 1$ but
$S_0(2) = \{1\}$.

Source: the forward direction of the first equivalence (for `t ≥ 1`) is proved as
`S_eq_singleton_zero_of_maxLength_eq` in
`FormalizedPapers/NumberTheory/BaraskarGokhaleJainKiezun2026`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 19. -/
public theorem_wanted pierce_maxLength_eq_succ_iff (n t : ℕ) (hn : 3 ≤ n) :
    (PierceExpansion.maxLength n = t + 1 ↔ iteratedRemainderSet t n = {0}) ∧
      (PierceExpansion.maxLength n = t + 1 ↔ (iteratedRemainderSet t n).card = 1 ∧
        ∀ j, 1 ≤ j → iteratedRemainderSet (t + j) n = ∅)

end

end MetaMathlibExt
