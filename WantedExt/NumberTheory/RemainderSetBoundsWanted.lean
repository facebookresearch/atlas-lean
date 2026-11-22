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

/-- The remainder set `S(n) = {n mod k : k ∈ {1, …, ⌊n/2⌋}}`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `S(n)`). -/
public def remainderSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n / 2)).image (n % ·)

/-- The number of distinct remainders `s(n) = |S(n)|` (OEIS A283190).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `s(n)`). -/
public def remainderCount (n : ℕ) : ℕ :=
  (remainderSet n).card

/-- `S(11) = {0, 1, 2, 3}`, so `s(11) = 4` (Table 1 of the paper).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Table 1. -/
public theorem remainderCount_eleven : remainderCount 11 = 4 := by decide

/-- `s(12) = 2`, the drop from `s(11) = 4` (Table 1 of the paper).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Table 1. -/
public theorem remainderCount_twelve : remainderCount 12 = 2 := by decide

/-- The limiting constant
`c = Σ_{p prime} 1/(p(p+1)) · ∏_{q prime, q < p} (1 - 1/q) ≈ 0.2296`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, equation `eq:asymp`. -/
public noncomputable def remainderConstant : ℝ :=
  ∑' p : Nat.Primes, (1 / ((p : ℝ) * ((p : ℝ) + 1))) *
    ∏ q ∈ (Finset.range p).filter Nat.Prime, (1 - 1 / (q : ℝ))

/-- Theorem 1: `s(n) = c n + O(n / (log n · log log n))`, and in particular
`s(n)/n → c`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Theorem 1 (`thm:asymp`). -/
public theorem_wanted remainderCount_asymptotic :
    (fun n : ℕ => (remainderCount n : ℝ) - remainderConstant * n) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) / (Real.log n * Real.log (Real.log n))) ∧
      Filter.Tendsto (fun n : ℕ => (remainderCount n : ℝ) / n) Filter.atTop
        (nhds remainderConstant)

/-- Proposition 17: `liminf_{n→∞} (s(n+1) - s(n)) = -∞`, i.e. for every `M` there are
infinitely many `n` with `s(n+1) + M ≤ s(n)`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Proposition 17 (`prop:diffs_unbounded`). -/
public theorem_wanted remainderCount_drops_unbounded (M : ℕ) :
    ∃ᶠ n in Filter.atTop, remainderCount (n + 1) + M ≤ remainderCount n

/-- Theorem 2: for `n ≥ 1`, `s(n) - O(log log n) ≤ s(n+1) ≤ s(n) + 1`, and
`liminf (s(n+1) - s(n)) = -∞`. The `O(log log n)` term is a constant multiple of
`log log n` for all large `n` (`log log n ≤ 0` for `n ≤ 2`).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Theorem 2 (`thm:diffs`). -/
public theorem_wanted remainderCount_consecutive_differences :
    (∀ n, 1 ≤ n → remainderCount (n + 1) ≤ remainderCount n + 1) ∧
      (∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
        (remainderCount n : ℝ) - C * Real.log (Real.log n) ≤ remainderCount (n + 1)) ∧
      ∀ M : ℕ, ∃ᶠ n in Filter.atTop, remainderCount (n + 1) + M ≤ remainderCount n

/-- Lemma 6: for positive integers `a, t` and a prime `p`, let `D_p` be the integers divisible
by `p` and by no smaller prime. Then
`|D_p ∩ [a+1, a+t]| = t · (1/p) · ∏_{p' < p prime} (1 - 1/p') + E(a,t,p)` with
`|E(a,t,p)| ≤ 2^{π(p-1)}`; the error term is the difference of the two sides.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 6 (`lem:Dp`). -/
public theorem_wanted card_leastPrimeFactor_interval_error {a t p : ℕ} (ha : 0 < a)
    (ht : 0 < t) (hp : p.Prime) :
    |((((Finset.Icc (a + 1) (a + t)).filter
          (fun m => p ∣ m ∧ ∀ q < p, q.Prime → ¬ q ∣ m)).card : ℕ) : ℝ) -
        t * (1 / (p : ℝ)) * ∏ q ∈ (Finset.range p).filter Nat.Prime, (1 - 1 / (q : ℝ))| ≤
      2 ^ Nat.primeCounting (p - 1)

/-- Lemma 7: `π(n) ≤ 1.3 · n / log n` for every `n ≥ 2`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 7 (`lem:primecounting_ub`). -/
public theorem_wanted primeCounting_le_thirteen_tenths {n : ℕ} (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ 13 / 10 * n / Real.log n

/-- Lemma 8: `Σ_{p > n prime} 1/p² = O(1/(n log n))`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 8 (`lem:psquared_sum_est`). -/
public theorem_wanted tsum_inv_sq_primes_gt_isBigO :
    (fun n : ℕ => ∑' p : {p : ℕ // p.Prime ∧ n < p}, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2)
      =O[Filter.atTop] (fun n : ℕ => 1 / ((n : ℝ) * Real.log n))

/-- The iterated remainder sets: `S_0(n) = {1, …, ⌊n/2⌋}` and
`S_j(n) = {n mod k : k ∈ S_{j-1}(n) ∖ {0}}` for `j ≥ 1`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 2 (definition of `S_j(n)`). -/
public def iteratedRemainderSet : ℕ → ℕ → Finset ℕ
  | 0, n => Finset.Icc 1 (n / 2)
  | j + 1, n => ((iteratedRemainderSet j n).erase 0).image (n % ·)

/-- `S_1(n) = S(n)`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 2 (`S(n) = S_1(n)`). -/
public theorem iteratedRemainderSet_one (n : ℕ) : iteratedRemainderSet 1 n = remainderSet n := by
  simp [iteratedRemainderSet, remainderSet]

/-- `S_6(35) = {0}` and `S_7(35) = ∅`, computed from the definition.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 2 (definition of `S_j(n)`). -/
public theorem iteratedRemainderSet_thirtyFive :
    iteratedRemainderSet 6 35 = {0} ∧ iteratedRemainderSet 7 35 = ∅ := by
  decide

/-- Lemma 19, corrected index: for `n ≥ 3` and `t ≥ 0`, the following are equivalent:
`P(n) = t + 1`; `S_t(n) = {0}`; `|S_t(n)| = 1` and `|S_{t+j}(n)| = 0` for all `j ≥ 1`.
Here `P(n) = max_{1 ≤ a ≤ n} P(n, a)` is `PierceExpansion.maxLength n` (`P(n, a)` the index
`t` with `a_t = 0` for `a_0 = a`, `a_{j+1} = n mod a_j`).
The paper prints `P(n) = t ⟺ S_{t+1}(n) = {0}`, which fails for every `n ≥ 3`
(e.g. `P(5) = 3` with `S_4(5) = ∅` and `S_2(5) = {0}`); its proof derives the lemma from
Lemma 18 (`r ∈ S_j(n)` iff some `⌊n/2⌋ + 1 ≤ a ≤ n` has `a_{j+1} = r`), which gives the
index `P(n) - 1`. Lemma 18, and hence this lemma, needs `n ≥ 3`: `P(2) = 1` but
`S_0(2) = {1}`. The forward direction of the first equivalence (for `t ≥ 1`) is proved as
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
