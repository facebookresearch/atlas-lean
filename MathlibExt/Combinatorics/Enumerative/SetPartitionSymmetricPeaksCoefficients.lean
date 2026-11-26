/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import MathlibExt.Combinatorics.Enumerative.SetPartitionSymmetricPeaks
import MathlibExt.Combinatorics.Enumerative.SetPartitionPeaks
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Coefficients of the symmetric peak generating function

We extract the total number of symmetric peaks at fixed length and block count. The counting
series has Stirling numbers of the second kind as coefficients, and each geometric factor
contributes a finite convolution.

## References

* Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set Partition*,
  INTEGERS 26 (2026), Article A8, pp. 1–10, Lemma 1 and Corollary 1,
  <https://math.colgate.edu/~integers/aa8/aa8.pdf>.
-/

open Finset PowerSeries

namespace MetaMathlibExt

open symmetricPeaks_derivative_generatingFunction (partitionWords card_partitionWords)

private noncomputable def partitionCountSeries (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)

private lemma coeff_partitionCountSeries (n k : ℕ) :
    coeff n (partitionCountSeries k) = (Nat.stirlingSecond n k : ℤ) := by
  rw [partitionCountSeries, coeff_mk]
  have hwords : partitionWords n k =
      univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w) := by
    ext w
    simp [partitionWords, IsSurjectiveRestrictedGrowthString]
  rw [← hwords, card_partitionWords]

private noncomputable def geometric (j : ℕ) : ℤ⟦X⟧ :=
  invOfUnit (1 - (j : ℤ⟦X⟧) * X) 1

private lemma coeff_geometric (j n : ℕ) : coeff n (geometric j) = (j : ℤ) ^ n := by
  induction n with
  | zero => simp [geometric, coeff_zero_eq_constantCoeff_apply]
  | succ n ih =>
    have h : (1 - (j : ℤ⟦X⟧) * X) * geometric j = 1 := mul_invOfUnit _ _ (by simp)
    have hc := congrArg (coeff (n + 1)) h
    simp only [sub_mul, one_mul, mul_assoc, map_sub, coeff_natCast_mul, coeff_succ_X_mul,
      coeff_one, Nat.succ_ne_zero, ite_false] at hc
    rw [sub_eq_zero.mp hc, ih, pow_succ']

private lemma coeff_X_partitionCountSeries (n k : ℕ) :
    coeff n (((k - 1 : ℕ) : ℤ⟦X⟧) * X * partitionCountSeries k) =
      ((k - 1 : ℕ) : ℤ) * Nat.stirlingSecond (n - 1) k := by
  rw [mul_assoc, coeff_natCast_mul]
  cases n with
  | zero => cases k <;> simp [coeff_zero_X_mul, Nat.stirlingSecond_zero_succ]
  | succ n => rw [coeff_succ_X_mul, coeff_partitionCountSeries, Nat.succ_sub_one]

-- Only the degrees up to `n - k` of the shifted geometric series can contribute.
private lemma coeff_shifted_geometric (n k j : ℕ) :
    coeff n (X ^ 3 * (geometric j * partitionCountSeries k)) =
      ∑ i ∈ Icc 3 (n - k), (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
  calc
    _ = ∑ i ∈ Icc 3 n, (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
      rw [coeff_X_pow_mul']
      by_cases hn : 3 ≤ n
      · rw [ite_eq_left hn, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, show n + 1 - 3 = n - 3 + 1 by omega]
        apply sum_congr rfl
        intro i _
        simp only [coeff_geometric, coeff_partitionCountSeries, Nat.add_sub_cancel_left,
          Nat.sub_sub]
      · rw [ite_eq_right hn, Icc_eq_empty hn, sum_empty]
    _ = _ := by
      symm
      apply sum_subset (Icc_subset_Icc_right (Nat.sub_le n k))
      intro i hi hni
      simp only [mem_Icc] at hi hni
      rw [Nat.stirlingSecond_eq_zero_of_lt (show n - i < k by omega), Nat.cast_zero, mul_zero]

private lemma coeff_peak_contribution (n k j : ℕ) :
    coeff n (partitionCountSeries k * (X ^ 3 * (j.choose 2 : ℤ⟦X⟧) * geometric j)) =
      (j.choose 2 : ℤ) * ∑ i ∈ Icc 3 (n - k),
        (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
  rw [show partitionCountSeries k * (X ^ 3 * (j.choose 2 : ℤ⟦X⟧) * geometric j) =
      (j.choose 2 : ℤ⟦X⟧) * (X ^ 3 * (geometric j * partitionCountSeries k)) by ac_rfl,
    coeff_natCast_mul, coeff_shifted_geometric]

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
public theorem sum_symmetricPeakCount_setPartitions (n k : ℕ) :
    ∑ w ∈ univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        symmetricPeakCount (List.ofFn fun i => (w i : ℕ)) =
      (k - 1) * Nat.stirlingSecond (n - 1) k +
        ∑ j ∈ Icc 2 k, j.choose 2 *
          ∑ i ∈ Icc 3 (n - k), j ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
  have h := congrArg (coeff n) (symmetricPeaks_derivative_generatingFunction k)
  change _ = coeff n (((k - 1 : ℕ) : ℤ⟦X⟧) * X * partitionCountSeries k +
    partitionCountSeries k * ∑ j ∈ Icc 1 k, X ^ 3 * (j.choose 2 : ℤ⟦X⟧) * geometric j) at h
  simp only [coeff_mk, map_add, mul_sum, map_sum] at h
  simp only [coeff_X_partitionCountSeries, coeff_peak_contribution] at h
  have hsum :
      (∑ j ∈ Icc 2 k, (j.choose 2 : ℤ) * ∑ i ∈ Icc 3 (n - k),
          (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k) =
        ∑ j ∈ Icc 1 k, (j.choose 2 : ℤ) * ∑ i ∈ Icc 3 (n - k),
          (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
    apply sum_subset (Icc_subset_Icc_left (by decide))
    intro j hj hj'
    have : j = 1 := by simp only [mem_Icc] at hj hj'; omega
    subst j
    simp
  rw [← hsum] at h
  apply Int.ofNat_inj.mp
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow] using h

end MetaMathlibExt
