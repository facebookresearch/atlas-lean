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

/-- The number of non-symmetric peaks of a word: consecutive triples `a b c` with `a < b > c` and
`a ≠ c` (companion of `symmetricPeakCount`, which counts the triples with `a = c`).

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Section 1. -/
def nonSymmetricPeakCount : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a < b ∧ c < b ∧ a ≠ c then 1 else 0) + nonSymmetricPeakCount (b :: c :: t)
  | _ => 0

/-- The paper's example word `1322141251` has one symmetric peak (`141`) and two non-symmetric
peaks (`132`, `251`).

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Section 1. -/
theorem symmetricPeakCount_nonSymmetricPeakCount_example :
    symmetricPeakCount [1, 3, 2, 2, 1, 4, 1, 2, 5, 1] = 1 ∧
      nonSymmetricPeakCount [1, 3, 2, 2, 1, 4, 1, 2, 5, 1] = 2 := by
  decide

/-- With `SP_k(x, 1) = ∑_n |P_{n,k}| x^n`,
`∂/∂q SP_k(x, q)|_{q=1} = (k - 1) x SP_k(x, 1) + SP_k(x, 1) ∑_{m=1}^k x^3 binom(m, 2)/(1 - mx)`,
where the left side is `∑_n (∑_{π ∈ P_{n,k}} sp(π)) x^n`; integer power series, `1/(1 - mx)` as
`invOfUnit`, `k - 1` truncated at `0`.

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

/-- `∂/∂q NSP_k(x, q)|_{q=1} = binom(k-1, 2) x NSP_k(x, 1)
+ NSP_k(x, 1) ∑_{m=3}^k 2x^3 binom(m, 3)/(1 - mx)`, with `NSP_k(x, 1) = ∑_n |P_{n,k}| x^n` and the
left side `∑_n (∑_{π ∈ P_{n,k}} nsp(π)) x^n`; integer power series, `1/(1 - mx)` as `invOfUnit`.

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

/-- The total number of symmetric peaks over all partitions of `[1, n]` with exactly `k` blocks
is `(k - 1) S_{n-1,k} + ∑_{j=2}^k binom(j, 2) ∑_{i=3}^{n-k} j^{i-3} S_{n-i,k}`.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Corollary 1 (`integers-2026-A8-cor-1`). -/
public theorem_wanted sum_symmetricPeakCount_setPartitions (n k : ℕ) :
    ∑ w ∈ univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        symmetricPeakCount (List.ofFn fun i => (w i : ℕ)) =
      (k - 1) * Nat.stirlingSecond (n - 1) k +
        ∑ j ∈ Icc 2 k, j.choose 2 * ∑ i ∈ Icc 3 (n - k), j ^ (i - 3) * Nat.stirlingSecond (n - i) k

/-- The total number of non-symmetric peaks over all partitions of `[1, n]` with exactly `k`
blocks is `binom(k-1, 2) S_{n-1,k} + 2 ∑_{j=3}^k binom(j, 3) ∑_{i=3}^{n-k} j^{i-3} S_{n-i,k}`.

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
