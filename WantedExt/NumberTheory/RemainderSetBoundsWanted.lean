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
public import MathlibExt.NumberTheory.IteratedRemainderSet
public import MathlibExt.NumberTheory.PrimeSquareTail
public import MathlibExt.NumberTheory.RemainderSet
public import MathlibExt.NumberTheory.RemainderSetBoundsCardLeastPrimeFactorIntervalError
public import MathlibExt.NumberTheory.RemainderSetBoundsPrimeCounting

/-!
# Bounds for sets of remainders (statements)

Statement-only targets from Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of
Remainders*, Journal of Integer Sequences 29 (2026), Article 26.1.4.

`S(n) = {n mod k : 1 ≤ k ≤ ⌊n/2⌋}` and `s(n) = |S(n)|` (OEIS A283190). The paper's
structural lemmas, its `O(log log n)` drop bound, and its iterated-set bounds are proved in
`FormalizedPapers/NumberTheory/BaraskarVukusic2026` (there `S 1 n` is this `remainderSet n`);
`WantedExt` and `MathlibExt` may not import `FormalizedPapers`, so the set is restated in
`MathlibExt.NumberTheory.RemainderSet`, which also proves the theorem on consecutive
differences. This file states the asymptotic `s(n) = cn + O(n/(log n log log n))`.
The upper bound on the prime-counting function is proved in
`MathlibExt.NumberTheory.RemainderSetBoundsPrimeCounting`. The auxiliary lemma
`card_leastPrimeFactor_interval_error` is proved in
`MathlibExt.NumberTheory.RemainderSetBoundsCardLeastPrimeFactorIntervalError`.
The inverse-prime-square tail bound is proved in
`MathlibExt.NumberTheory.PrimeSquareTail`. The iterated remainder sets `S_j(n)` are defined, and
Lemma 19 (`S_j(n)` versus the Pierce length `P(n)`, in corrected form) is proved, in
`MathlibExt.NumberTheory.IteratedRemainderSet`.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
