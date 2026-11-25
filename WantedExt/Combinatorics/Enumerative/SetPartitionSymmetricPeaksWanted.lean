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
public import MathlibExt.Combinatorics.Enumerative.SetPartitionNonSymmetricPeaks
public import MathlibExt.Combinatorics.Enumerative.SetPartitionSymmetricPeaks

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
