/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.InfiniteDividendDiscount
import Mathlib.Tactic

/-!
# Tests for infinite dividend-discount identity

Tests for the infinite dividend-discount identity: constant dividends (`∑' t,
(1/2)^(t+1) = 1`) and zero dividends, plus the constant-dividend case via the
unconditional theorem.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.InfiniteDividendDiscount

open MathlibExt.Economics.Finance
open MathlibExt.Economics.Finance.InfiniteDividendDiscount

theorem geom_half_sum_Icc (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, (1/2:ℝ)^t = 1 - (1/2:ℝ)^n := by
  induction n with
  | zero =>
    rw [Finset.sum_eq_zero (fun x hx => by rw [Finset.mem_Icc] at hx; omega), pow_zero]
    norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, pow_succ]
    ring

theorem test_constantDividends : ∑' t, (1/2:ℝ)^(t+1) = 1 := by
  have hdisc : ∀ t, discountFactor (1:ℝ) t = (1/2:ℝ)^t := by
    intro t
    unfold discountFactor
    rw [(by norm_num : (1:ℝ) + 1 = 2), ← inv_pow, inv_eq_one_div]
  have hfinite : ∀ n, (fun _ : ℕ => (1:ℝ)) 0
      = presentValue (discountFactor 1) (Finset.Icc 1 n) (fun _ : ℕ => (1:ℝ))
        + discountFactor 1 n * (fun _ : ℕ => (1:ℝ)) n := by
    intro n
    simp only [presentValue, hdisc, mul_one]
    rw [geom_half_sum_Icc]
    ring
  have hvanish : Filter.Tendsto (fun n => discountFactor (1:ℝ) n * (fun _ : ℕ => (1:ℝ)) n)
      Filter.atTop (nhds 0) := by
    simp only [hdisc, mul_one]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnn : ∀ t, 0 ≤ (fun _ : ℕ => (1:ℝ)) (t + 1) := fun t => zero_le_one
  have h := dividendDiscountInfinite_of_finite (r := 1) (D := fun _ : ℕ => (1:ℝ))
    (P := fun _ : ℕ => (1:ℝ)) (by norm_num : (0:ℝ) < 1 + 1) hfinite hvanish hnn
  have h2 : HasSum (fun t => (1/2:ℝ)^(t+1)) 1 :=
    h.congr_fun (fun t => by simp [dividendTerm, hdisc])
  exact h2.tsum_eq

theorem test_zeroDividends : HasSum (dividendTerm 1 0) 0 := by
  have hfinite : ∀ n, (0 : ℕ → ℝ) 0
      = presentValue (discountFactor 1) (Finset.Icc 1 n) (0 : ℕ → ℝ)
        + discountFactor 1 n * (0 : ℕ → ℝ) n := by
    intro n
    simp [presentValue]
  have hvanish : Filter.Tendsto (fun n => discountFactor (1:ℝ) n * (0 : ℕ → ℝ) n)
      Filter.atTop (nhds 0) := by
    simp only [Pi.zero_apply, mul_zero]
    exact tendsto_const_nhds
  have hnn : ∀ t, 0 ≤ (0 : ℕ → ℝ) (t + 1) := fun t => by simp
  have h := dividendDiscountInfinite_of_finite (r := 1) (D := 0) (P := 0)
    (by norm_num : (0:ℝ) < 1 + 1) hfinite hvanish hnn
  exact h

/-! Test example: constant dividends via the unconditional theorem. -/

example : ∑' t, (1 / 2 : ℝ) ^ (t + 1) = 1 := by
  have hrec : ∀ t, (fun _ : ℕ => (1 : ℝ)) t
      = ((fun _ : ℕ => (1 : ℝ)) (t + 1) + (fun _ : ℕ => (1 : ℝ)) (t + 1)) / (1 + 1) := by
    intro t
    norm_num
  have hnn : ∀ t, 0 ≤ (fun _ : ℕ => (1 : ℝ)) (t + 1) := by
    intro t
    norm_num
  have hvanish : Filter.Tendsto
      (fun n => MathlibExt.Economics.Finance.discountFactor (1 : ℝ) n *
        (fun _ : ℕ => (1 : ℝ)) n) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => MathlibExt.Economics.Finance.discountFactor (1 : ℝ) n *
        (fun _ : ℕ => (1 : ℝ)) n) = (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
      funext n
      simp [MathlibExt.Economics.Finance.discountFactor, one_div, inv_pow]
      norm_num
    rw [heq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsum : HasSum
      (MathlibExt.Economics.Finance.InfiniteDividendDiscount.dividendTerm (1 : ℝ)
        (fun _ : ℕ => (1 : ℝ))) 1 :=
    MathlibExt.Economics.Finance.InfiniteDividendDiscount.dividendDiscountInfinite
      (by norm_num) hrec hvanish hnn
  have hfun : MathlibExt.Economics.Finance.InfiniteDividendDiscount.dividendTerm (1 : ℝ)
      (fun _ : ℕ => (1 : ℝ)) = (fun t => (1 / 2 : ℝ) ^ (t + 1)) := by
    funext t
    simp [MathlibExt.Economics.Finance.InfiniteDividendDiscount.dividendTerm,
      MathlibExt.Economics.Finance.discountFactor, one_div, inv_pow]
    norm_num
  rw [hfun] at hsum
  exact hsum.tsum_eq


end MathlibExtTest.Economics.Finance.InfiniteDividendDiscount
