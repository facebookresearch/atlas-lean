/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
public import WantedExt.Combinatorics.Enumerative.SymmetricPeaksCompositionsWanted

/-!
# Symmetric and non-symmetric peaks in set partitions

Statements from Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8.

A partition of `[1, n]` with exactly `k` blocks is encoded by its canonical sequential form, a
surjective restricted-growth string `w : Fin n → Fin k` (`IsSurjectiveRestrictedGrowthString`;
block `i + 1` of the paper is the label `i`). A peak is a consecutive triple `a < b > c`; it is
symmetric if `a = c` (`symmetricPeakCount`, shared with the authors' compositions paper) and
non-symmetric otherwise; both are counted on the word `List.ofFn w` of labels (the shift of
labels does not change peaks). `S_{n,k}` is `Nat.stirlingSecond n k`.
-/

open Finset PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Non-symmetric peaks of a word.** For a word $w = w_1 w_2 \cdots w_\ell$ of natural numbers,
a non-symmetric peak is a position $i$ with $1 < i < \ell$ such that $w_{i-1} < w_i$,
$w_{i+1} < w_i$ and $w_{i-1} \ne w_{i+1}$. The non-symmetric peak count of $w$ is the number of
such positions; in particular it is $0$ when $\ell < 3$.

A peak with $w_{i-1} = w_{i+1}$ is a symmetric peak instead.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Section 1. -/
def nonSymmetricPeakCount : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a < b ∧ c < b ∧ a ≠ c then 1 else 0) + nonSymmetricPeakCount (b :: c :: t)
  | _ => 0

/-- **Peaks of the word $1322141251$.** The word $1322141251$ (the list
$1, 3, 2, 2, 1, 4, 1, 2, 5, 1$) has exactly one symmetric peak, the factor $141$, and exactly two
non-symmetric peaks, the factors $132$ and $251$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Section 1. -/
theorem symmetricPeakCount_nonSymmetricPeakCount_example :
    symmetricPeakCount [1, 3, 2, 2, 1, 4, 1, 2, 5, 1] = 1 ∧
      nonSymmetricPeakCount [1, 3, 2, 2, 1, 4, 1, 2, 5, 1] = 2 := by
  decide

/-- **Generating function for the total number of symmetric peaks in set partitions.** Fix
$k \in \mathbb{N}$ and, for each $n$, let $P_{n,k}$ be the set of surjective restricted-growth
strings of length $n$ with letters in $\{0, \dots, k-1\}$; these encode the partitions of
$\{1, \dots, n\}$ into exactly $k$ blocks. For $w \in P_{n,k}$ let $\operatorname{sp}(w)$ be the
number of symmetric peaks of $w$. In the ring $\mathbb{Z}[[x]]$ of formal power series let
$F_k(x) = \sum_{n \ge 0} |P_{n,k}| x^n$. Then
$$
\sum_{n \ge 0} \Big(\sum_{w \in P_{n,k}} \operatorname{sp}(w)\Big) x^n =
\max(k - 1, 0)\, x F_k(x) + F_k(x) \sum_{m=1}^{k} \binom{m}{2} \frac{x^3}{1 - m x},
$$
where $1/(1 - m x)$ is the inverse of $1 - m x$ in $\mathbb{Z}[[x]]$.

If $SP_k(x, q) = \sum_{n \ge 0} \sum_{w \in P_{n,k}} q^{\operatorname{sp}(w)} x^n$, then
$F_k(x) = SP_k(x, 1)$ and the left side is the derivative of $SP_k(x, q)$ in $q$ at $q = 1$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Lemma 1 (`integers-2026-A8-lem-1`). -/
public theorem_wanted symmetricPeaks_derivative_generatingFunction (k : ℕ) :
    let SP : ℤ⟦X⟧ := PowerSeries.mk fun n =>
      ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)
    PowerSeries.mk (fun n => ((∑ w ∈ univ.filter
        (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        symmetricPeakCount (List.ofFn fun i => (w i : ℕ)) : ℕ) : ℤ)) =
      ((k - 1 : ℕ) : ℤ⟦X⟧) * X * SP +
        SP * ∑ m ∈ Icc 1 k, X ^ 3 * ((m.choose 2 : ℕ) : ℤ⟦X⟧) *
          invOfUnit (1 - ((m : ℕ) : ℤ⟦X⟧) * X) 1

/-- **Generating function for the total number of non-symmetric peaks in set partitions.** Fix
$k \in \mathbb{N}$ and, for each $n$, let $P_{n,k}$ be the set of surjective restricted-growth
strings of length $n$ with letters in $\{0, \dots, k-1\}$; these encode the partitions of
$\{1, \dots, n\}$ into exactly $k$ blocks. For $w \in P_{n,k}$ let $\operatorname{nsp}(w)$ be the
number of non-symmetric peaks of $w$. In the ring $\mathbb{Z}[[x]]$ of formal power series let
$F_k(x) = \sum_{n \ge 0} |P_{n,k}| x^n$. Then
$$
\sum_{n \ge 0} \Big(\sum_{w \in P_{n,k}} \operatorname{nsp}(w)\Big) x^n =
\binom{k - 1}{2} x F_k(x) + F_k(x) \sum_{m=3}^{k} 2 \binom{m}{3} \frac{x^3}{1 - m x},
$$
where $k - 1$ is read as $0$ when $k = 0$ and $1/(1 - m x)$ is the inverse of $1 - m x$ in
$\mathbb{Z}[[x]]$.

If $NSP_k(x, q) = \sum_{n \ge 0} \sum_{w \in P_{n,k}} q^{\operatorname{nsp}(w)} x^n$, then
$F_k(x) = NSP_k(x, 1)$ and the left side is the derivative of $NSP_k(x, q)$ in $q$ at $q = 1$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Lemma 2 (`integers-2026-A8-lem-2`). -/
public theorem_wanted nonSymmetricPeaks_derivative_generatingFunction (k : ℕ) :
    let NSP : ℤ⟦X⟧ := PowerSeries.mk fun n =>
      ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)
    PowerSeries.mk (fun n => ((∑ w ∈ univ.filter
        (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        nonSymmetricPeakCount (List.ofFn fun i => (w i : ℕ)) : ℕ) : ℤ)) =
      (((k - 1).choose 2 : ℕ) : ℤ⟦X⟧) * X * NSP +
        NSP * ∑ m ∈ Icc 3 k, 2 * X ^ 3 * ((m.choose 3 : ℕ) : ℤ⟦X⟧) *
          invOfUnit (1 - ((m : ℕ) : ℤ⟦X⟧) * X) 1

/-- **Total number of symmetric peaks over set partitions with $k$ blocks.** For natural numbers
$n$ and $k$, let $P_{n,k}$ be the set of surjective restricted-growth strings of length $n$ with
letters in $\{0, \dots, k-1\}$ (these encode the partitions of $\{1, \dots, n\}$ into exactly $k$
blocks). For $w \in P_{n,k}$ let $\operatorname{sp}(w)$ be the number of symmetric peaks of $w$,
and denote by $S(a, b)$ the Stirling numbers of the second kind. Then
$$
\sum_{w \in P_{n,k}} \operatorname{sp}(w) = (k - 1)\, S(n - 1, k) +
\sum_{j=2}^{k} \binom{j}{2} \sum_{i=3}^{n-k} j^{i-3}\, S(n - i, k),
$$
where the differences $k - 1$, $n - 1$ and $n - k$ of natural numbers are truncated at $0$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Corollary 1 (`integers-2026-A8-cor-1`). -/
public theorem_wanted sum_symmetricPeakCount_setPartitions (n k : ℕ) :
    ∑ w ∈ univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        symmetricPeakCount (List.ofFn fun i => (w i : ℕ)) =
      (k - 1) * Nat.stirlingSecond (n - 1) k +
        ∑ j ∈ Icc 2 k, j.choose 2 * ∑ i ∈ Icc 3 (n - k), j ^ (i - 3) * Nat.stirlingSecond (n - i) k

/-- **Total number of non-symmetric peaks over set partitions with $k$ blocks.** For natural
numbers $n$ and $k$, let $P_{n,k}$ be the set of surjective restricted-growth strings of length $n$
with letters in $\{0, \dots, k-1\}$ (these encode the partitions of $\{1, \dots, n\}$ into exactly
$k$ blocks). For $w \in P_{n,k}$ let $\operatorname{nsp}(w)$ be the number of non-symmetric peaks
of $w$, and denote by $S(a, b)$ the Stirling numbers of the second kind. Then
$$
\sum_{w \in P_{n,k}} \operatorname{nsp}(w) = \binom{k - 1}{2} S(n - 1, k) +
2 \sum_{j=3}^{k} \binom{j}{3} \sum_{i=3}^{n-k} j^{i-3}\, S(n - i, k),
$$
where the differences $k - 1$, $n - 1$ and $n - k$ of natural numbers are truncated at $0$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Corollary 2 (`integers-2026-A8-cor-2`). -/
public theorem_wanted sum_nonSymmetricPeakCount_setPartitions (n k : ℕ) :
    ∑ w ∈ univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        nonSymmetricPeakCount (List.ofFn fun i => (w i : ℕ)) =
      (k - 1).choose 2 * Nat.stirlingSecond (n - 1) k +
        2 * ∑ j ∈ Icc 3 k, j.choose 3 *
          ∑ i ∈ Icc 3 (n - k), j ^ (i - 3) * Nat.stirlingSecond (n - i) k

end

end MetaMathlibExt
