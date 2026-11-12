/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.FiniteDividendDiscount
import Mathlib.Tactic

/-!
# Tests for finite dividend-discount identity

Tests for the finite dividend-discount identity: concrete `n = 2` examples at
`r = 1/10` (`P 0 = 2410/121`) and `r = 0` (`P 0 = 15`), and the generic `n = 1` corollary.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.FiniteDividendDiscount

open MathlibExt.Economics.Finance
open MathlibExt.Economics.Finance.FiniteDividendDiscount

/-- Helper: the two-point interval as an explicit pair. -/
theorem Icc_1_2_eq : Finset.Icc (1 : ℕ) 2 = {1, 2} := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Test 1: concrete `n = 2` with `r = 1/10`. -/
theorem finiteDividendDiscount_n2_concrete (D P : ℕ → ℝ)
    (hD : D = fun t => if t = 1 then (11 : ℝ) else if t = 2 then 12 else 0)
    (hP : P = fun t => if t = 0 then (2410 / 121 : ℝ) else if t = 1 then 120 / 11 else 0) :
    P 0 = 2410 / 121 := by
  have hr : (1 : ℝ) + 1 / 10 ≠ 0 := by norm_num
  have hrec : ∀ t, P t = (D (t + 1) + P (t + 1)) / (1 + (1 / 10 : ℝ)) := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      norm_num [hD, hP]
    · by_cases ht1 : t = 1
      · subst ht1
        norm_num [hD, hP]
      · have h2 : 2 ≤ t := by omega
        have hne0 : t + 1 ≠ 0 := by omega
        have hne1 : t + 1 ≠ 1 := by omega
        have hne2 : t + 1 ≠ 2 := by omega
        have hPt : P t = 0 := by simp only [hP, ite_eq_right ht0, ite_eq_right ht1]
        have hDt1 : D (t + 1) = 0 := by simp only [hD, ite_eq_right hne1, ite_eq_right hne2]
        have hPt1 : P (t + 1) = 0 := by simp only [hP, ite_eq_right hne0, ite_eq_right hne1]
        rw [hPt, hDt1, hPt1]
        norm_num
  have hD1 : D 1 = (11 : ℝ) := by simp [hD]
  have hD2 : D 2 = (12 : ℝ) := by simp [hD]
  have hP2 : P 2 = (0 : ℝ) := by simp [hP]
  have h := finiteDividendDiscount (r := 1 / 10) hr (D := D) (P := P) hrec 2
  rw [h, Icc_1_2_eq]
  simp only [presentValue, Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide),
    hD1, hD2, hP2, discountFactor]
  norm_num

/-- Test 2: zero rate `r = 0` with `n = 2`. -/
theorem finiteDividendDiscount_zeroRate (D P : ℕ → ℝ)
    (hD : D = fun t => if t = 1 then (5 : ℝ) else if t = 2 then 7 else 0)
    (hP : P = fun t => if t = 0 then (15 : ℝ) else if t = 1 then 10 else 3) :
    P 0 = 15 := by
  have hr : (1 : ℝ) + 0 ≠ 0 := by norm_num
  have hrec : ∀ t, P t = (D (t + 1) + P (t + 1)) / (1 + (0 : ℝ)) := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      norm_num [hD, hP]
    · by_cases ht1 : t = 1
      · subst ht1
        norm_num [hD, hP]
      · have h2 : 2 ≤ t := by omega
        have hne0 : t + 1 ≠ 0 := by omega
        have hne1 : t + 1 ≠ 1 := by omega
        have hne2 : t + 1 ≠ 2 := by omega
        have hPt : P t = 3 := by simp only [hP, ite_eq_right ht0, ite_eq_right ht1]
        have hDt1 : D (t + 1) = 0 := by simp only [hD, ite_eq_right hne1, ite_eq_right hne2]
        have hPt1 : P (t + 1) = 3 := by simp only [hP, ite_eq_right hne0, ite_eq_right hne1]
        rw [hPt, hDt1, hPt1]
        norm_num
  have hD1 : D 1 = (5 : ℝ) := by simp [hD]
  have hD2 : D 2 = (7 : ℝ) := by simp [hD]
  have hP2 : P 2 = (3 : ℝ) := by simp [hP]
  have h := finiteDividendDiscount (r := 0) hr (D := D) (P := P) hrec 2
  rw [h, Icc_1_2_eq]
  simp only [presentValue, Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide),
    hD1, hD2, hP2, discountFactor]
  norm_num

/-- Test 3: generic `n = 1` corollary from the recursion at `t = 0` alone. -/
theorem finiteDividendDiscount_n1 {r : ℝ} {D P : ℕ → ℝ}
    (h0 : P 0 = (D 1 + P 1) / (1 + r)) :
    P 0 = discountFactor r 1 * D 1 + discountFactor r 1 * P 1 := by
  simp only [discountFactor, pow_one, h0, div_eq_inv_mul, mul_add]


end MathlibExtTest.Economics.Finance.FiniteDividendDiscount
