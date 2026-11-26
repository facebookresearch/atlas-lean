/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer

/-!
# Lee's identity for Stirling numbers of the first kind from higher columns

The two expansions of the rising factorial of order `n + 1` give an identity
for the coefficient of degree `k`. Separating the two lowest contributing
columns in the shifted expansion gives Lee's formula.
-/

set_option autoImplicit false

open Finset Polynomial

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- Compare coefficients in the identity for the rising factorial at `X + 1`. -/
private theorem stirlingFirst_succ_eq_sum_Ico (n r : ℕ) (hr : r ≤ n) :
    (Nat.stirlingFirst (n + 1) (r + 1) : ℤ) =
      ∑ i ∈ Ico r (n + 1), (Nat.stirlingFirst n i : ℤ) * i.choose r := by
  calc
    _ = (ascPochhammer ℤ (n + 1)).coeff (r + 1) := by
      rw [← Nat.sum_stirlingFirst_mul_X_pow, finsetSum_coeff]
      simp [coeff_X_pow, mul_ite, hr]
    _ = ∑ i ∈ range (n + 1), (Nat.stirlingFirst n i : ℤ) * i.choose r := by
      rw [ascPochhammer_succ_left, coeff_X_mul, ← Nat.sum_stirlingFirst_mul_X_pow]
      simp [Polynomial.sum_comp, mul_comp, pow_comp, finsetSum_coeff, coeff_X_add_one_pow]
    _ = _ := by
      symm
      apply sum_subset (fun i hi => mem_range.mpr (mem_Ico.mp hi).2)
      intro i hi hri
      have hir : i < r := by simpa [mem_Ico, mem_range.mp hi] using hri
      simp [Nat.choose_eq_zero_of_lt hir]

/-- **Lee's identity for Stirling numbers of the first kind from higher columns.** Write $c(n, k)$
for the unsigned Stirling number of the first kind, the number of permutations of $n$ elements
with exactly $k$ cycles. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:
$$(n - k)\, c(n, k) = \sum_{j=2}^{n-k+1} \binom{k+j-1}{j}\, c(n, k+j-1).$$

This is Lee's Theorem 14 with the denominator $n - k$ cleared.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 14
(TeX label `thm:dwfmc`). -/
public theorem stirlingFirst_mul_sub_eq_sum_stirlingFirst_choose
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingFirst n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.stirlingFirst n (k + j - 1) : ℤ) *
          (Nat.choose (k + j - 1) j : ℤ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h := stirlingFirst_succ_eq_sum_Ico n r (by omega)
  rw [sum_eq_sum_Ico_succ_bot (a := r) (by omega),
    sum_eq_sum_Ico_succ_bot (a := r + 1) (by omega)] at h
  simp only [Nat.stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul, Nat.choose_self,
    Nat.choose_succ_self_right, Nat.cast_one, mul_one] at h
  have htail :
      (∑ i ∈ Ico (r + 1 + 1) (n + 1), (Nat.stirlingFirst n i : ℤ) * i.choose r) =
      ∑ j ∈ Icc 2 (n - (r + 1) + 1),
        (Nat.stirlingFirst n (r + j) : ℤ) * (r + j).choose j := by
    rw [← Ico_add_one_right_eq_Icc]
    simp_rw [← Nat.choose_symm_add (a := r)]
    rw [sum_Ico_add (fun i => (Nat.stirlingFirst n i : ℤ) * i.choose r)]
    congr 2 <;> omega
  rw [htail] at h
  simp only [Nat.succ_add_sub_one, Nat.cast_succ]
  linarith

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted
