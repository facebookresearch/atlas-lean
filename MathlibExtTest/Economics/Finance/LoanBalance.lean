/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.LoanBalance
import Mathlib.Tactic.NormNum

/-!
# Tests for loan balances

A loan of `3` at `r = 1` repaid by two payments of `4`: after one payment both balances are
`2`; the prospective balance after the last payment is `0` and the retrospective balance
before any payment is the loan.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.LoanBalance

open MathlibExt.Economics.Finance

example : (3 : ℝ) = presentValue (discountFactor 1) (Finset.Icc 1 2) (fun _ => 4) := by
  have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
  have hmem : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  simp only [presentValue, hIcc, Finset.sum_insert hmem, Finset.sum_singleton,
    discountFactor]
  norm_num

example : retrospectiveBalance (1 : ℝ) 3 4 1 = prospectiveBalance (1 : ℝ) 4 2 1 := by
  have hL : (3 : ℝ) = presentValue (discountFactor 1) (Finset.Icc 1 2) (fun _ => 4) := by
    have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
    have hmem : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
    simp only [presentValue, hIcc, Finset.sum_insert hmem, Finset.sum_singleton,
      discountFactor]
    norm_num
  exact retrospectiveBalance_eq_prospectiveBalance (1 : ℝ) (3 : ℝ) (4 : ℝ) 2 1
    (by norm_num) (by decide) hL

example : retrospectiveBalance (1 : ℝ) 3 4 1 = 2 := by
  simp only [retrospectiveBalance, Finset.sum_range_one]
  norm_num

example : prospectiveBalance (1 : ℝ) 4 2 1 = 2 := by
  have hsub : (2 : ℕ) - 1 = 1 := by decide
  have hIcc : Finset.Icc (1 : ℕ) 1 = {1} := Finset.Icc_self 1
  simp only [prospectiveBalance, presentValue, hsub, hIcc, Finset.sum_singleton,
    discountFactor]
  norm_num

example (r P : ℝ) (n : ℕ) : prospectiveBalance r P n n = 0 := by
  have hempty : Finset.Icc (1 : ℕ) 0 = ∅ := Finset.Icc_eq_empty (by decide)
  simp only [prospectiveBalance, presentValue, Nat.sub_self, hempty, Finset.sum_empty]

example (r L P : ℝ) : retrospectiveBalance r L P 0 = L := by
  simp [retrospectiveBalance]

end MathlibExtTest.Economics.Finance.LoanBalance
