/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import MathlibExt.Combinatorics.Enumerative.SetPartitionNonSymmetricPeaks
import Mathlib.Algebra.BigOperators.Intervals
import MathlibExt.Combinatorics.Enumerative.SetPartitionPeaks

/-!
# Coefficients of the non-symmetric peak generating function

We extract the coefficients of the partition counting series multiplied by a linear term
and shifted geometric series. The Stirling numbers vanish below the block count, which
cuts off each convolution.

## References

* Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set Partition*,
  INTEGERS 26 (2026), Article A8, pp. 1–10, Lemma 2 and Corollary 2,
  <https://math.colgate.edu/~integers/aa8/aa8.pdf>.
* Walaa Asakly, *Enumerating symmetric and non-symmetric peaks in words*, Online Journal of
  Analytic Combinatorics 13 (2018), Article 2, pp. 1–7, proof of Theorem 5,
  <https://combinatorialpress.com/article/ojac/vol13/169.pdf>. The proof of Lemma 2 in the set
  partition paper cites this word-series derivative.
-/

open Finset PowerSeries

namespace MetaMathlibExt

open symmetricPeaks_derivative_generatingFunction (partitionWords card_partitionWords)

private noncomputable def partitionSeries (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)

private lemma coeff_partitionSeries (n k : ℕ) :
    coeff n (partitionSeries k) = (Nat.stirlingSecond n k : ℤ) := by
  rw [partitionSeries, coeff_mk]
  have hwords : partitionWords n k =
      univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w) := by
    ext w
    simp [partitionWords, IsSurjectiveRestrictedGrowthString]
  rw [← hwords, card_partitionWords]

private noncomputable def geometric (j : ℕ) : ℤ⟦X⟧ :=
  invOfUnit (1 - (j : ℤ⟦X⟧) * X) 1

private lemma coeff_geometric (j d : ℕ) : coeff d (geometric j) = (j : ℤ) ^ d := by
  induction d with
  | zero => simp [geometric, coeff_zero_eq_constantCoeff_apply]
  | succ d ih =>
    have h : (1 - (j : ℤ⟦X⟧) * X) * geometric j = 1 := mul_invOfUnit _ _ (by simp)
    have hc := congrArg (coeff (d + 1)) h
    simp only [sub_mul, one_mul, mul_assoc, map_sub, coeff_natCast_mul, coeff_succ_X_mul,
      coeff_one, Nat.succ_ne_zero, ite_false] at hc
    rw [sub_eq_zero.mp hc, ih, pow_succ']

private lemma coeff_linearTerm (n k : ℕ) :
    coeff n (((k - 1).choose 2 : ℤ⟦X⟧) * X * partitionSeries k) =
      ((k - 1).choose 2 : ℤ) * Nat.stirlingSecond (n - 1) k := by
  rw [mul_assoc, coeff_natCast_mul]
  cases n with
  | zero => cases k <;> simp [coeff_zero_X_mul, Nat.stirlingSecond_zero_succ]
  | succ n => rw [coeff_succ_X_mul, coeff_partitionSeries, Nat.succ_sub_one]

-- The degree i removed from n includes the shift by three.
private lemma coeff_geometricTerm (n k j : ℕ) :
    coeff n (X ^ 3 * (geometric j * partitionSeries k)) =
      ∑ i ∈ Icc 3 (n - k), (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
  calc
    _ = ∑ i ∈ Icc 3 n, (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
      rw [coeff_X_pow_mul']
      by_cases hn : 3 ≤ n
      · rw [ite_eq_left hn, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, show n + 1 - 3 = n - 3 + 1 by omega]
        refine sum_congr rfl fun i _ => ?_
        simp only [coeff_geometric, coeff_partitionSeries, Nat.add_sub_cancel_left, Nat.sub_sub]
      · rw [ite_eq_right hn, Icc_eq_empty hn, sum_empty]
    _ = _ := by
      symm
      refine sum_subset (Icc_subset_Icc_right (Nat.sub_le n k)) fun i hi hni => ?_
      simp only [mem_Icc] at hi hni
      rw [Nat.stirlingSecond_eq_zero_of_lt (show n - i < k by omega), Nat.cast_zero, mul_zero]

private lemma coeff_peakTerm (n k j : ℕ) :
    coeff n (partitionSeries k * (2 * X ^ 3 * (j.choose 3 : ℤ⟦X⟧) * geometric j)) =
      2 * ((j.choose 3 : ℤ) * ∑ i ∈ Icc 3 (n - k),
        (j : ℤ) ^ (i - 3) * Nat.stirlingSecond (n - i) k) := by
  rw [show partitionSeries k * (2 * X ^ 3 * (j.choose 3 : ℤ⟦X⟧) * geometric j) =
      2 * ((j.choose 3 : ℤ⟦X⟧) * (X ^ 3 * (geometric j * partitionSeries k))) by ac_rfl]
  rw [show (2 : ℤ⟦X⟧) = ((2 : ℕ) : ℤ⟦X⟧) by simp, coeff_natCast_mul,
    coeff_natCast_mul, coeff_geometricTerm]
  rfl

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
public theorem sum_nonSymmetricPeakCount_setPartitions (n k : ℕ) :
    ∑ w ∈ univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        nonSymmetricPeakCount (List.ofFn fun i => (w i : ℕ)) =
      (k - 1).choose 2 * Nat.stirlingSecond (n - 1) k +
        2 * ∑ j ∈ Icc 3 k, j.choose 3 *
          ∑ i ∈ Icc 3 (n - k), j ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
  have h := congrArg (coeff n) (nonSymmetricPeaks_derivative_generatingFunction k)
  change _ = coeff n (((k - 1).choose 2 : ℤ⟦X⟧) * X * partitionSeries k +
    partitionSeries k * ∑ j ∈ Icc 3 k, 2 * X ^ 3 * (j.choose 3 : ℤ⟦X⟧) * geometric j) at h
  simp only [coeff_mk, map_add, mul_sum, map_sum] at h
  simp only [coeff_linearTerm, coeff_peakTerm] at h
  rw [← mul_sum] at h
  exact Int.ofNat_inj.mp (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using h)

end MetaMathlibExt
