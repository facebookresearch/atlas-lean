/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.TakagiDNodeDyadicValue

/-! # Tests for the D-node formula for dyadic Takagi values -/

open Finset MetaMathlibExt

-- Evaluate the three-bit coefficient series independently: the first three terms read the
-- three bits, and the remaining coefficients count the ones among those bits.
private theorem takagi_eighths (r : ℕ) :
    takagiNewdef r 2 = (takagiEll r 2 2 : ℝ) / 4 + (takagiEll r 2 3 : ℝ) / 8 +
      ((takagiBit r 2 + takagiBit r 1 + takagiBit r 0 : ℕ) : ℝ) / 8 := by
  let f (i : ℕ) : ℝ := (takagiEll r 2 (i + 1) : ℝ) / 2 ^ (i + 1)
  have hzeros (j : ℕ) (hj : 3 ≤ j) : takagiBit r (2 - (j : ℤ)) = 0 :=
    takagiBit_neg _ _ (by omega)
  have htail (i : ℕ) : f (i + 3) =
      ((takagiBit r 2 + takagiBit r 1 + takagiBit r 0 : ℕ) : ℝ) / 8 / 2 / 2 ^ i := by
    have hprefix : (∑ j ∈ range (i + 3), takagiBit r (2 - (j : ℤ))) =
        ∑ j ∈ range 3, takagiBit r (2 - (j : ℤ)) := by
      symm
      exact sum_subset (range_mono (by omega)) fun j _ hj ↦
        hzeros j (by simpa using hj)
    dsimp only [f]
    rw [takagiEll_succ, hzeros _ (by omega), ite_eq_left rfl, hprefix,
      show i + 3 + 1 = 4 + i by omega, pow_add, div_div, div_div, ← mul_assoc]
    norm_num [sum_range_succ]
  have ht : HasSum (fun i ↦ f (i + 3))
      (((takagiBit r 2 + takagiBit r 1 + takagiBit r 0 : ℕ) : ℝ) / 8) := by
    simp_rw [htail]
    exact hasSum_geometric_two' _
  have hsum := (hasSum_nat_add_iff (f := f) 3).mp ht
  rw [takagiNewdef_eq]
  change (∑' i, f i) = _
  rw [hsum.tsum_eq]
  norm_num [sum_range_succ, f, takagiEll_one]
  ring

-- Both leading-bit branches and the right endpoint, using the public bit and count equations.
example : takagiNewdef 3 2 = 5 / 8 ∧ dcDNodes 11 = 5 := by
  constructor
  · norm_num [takagi_eighths, takagiEll_succ, takagiBit_eq,
      Nat.testBit_eq_decide_div_mod_eq, sum_range_succ]
  · rw [show 11 = 2 * 5 + 1 by decide, dcDNodes_two_mul_add_one (by decide)]
    norm_num [dcDNodes_small.2.2.2.1, dcDNodes_small.2.2.2.2.1]

example : takagiNewdef 7 2 = 3 / 8 ∧ dcDNodes 15 = 3 := by
  constructor
  · norm_num [takagi_eighths, takagiEll_succ, takagiBit_eq,
      Nat.testBit_eq_decide_div_mod_eq, sum_range_succ]
  · rw [show 15 = 2 * 7 + 1 by decide, dcDNodes_two_mul_add_one (by decide),
      show 7 + 1 = 2 * 4 by decide, dcDNodes_two_mul (by decide)]
    norm_num [dcDNodes_small.2.2.2.2.2, dcDNodes_small.2.2.1]

example : takagiNewdef 8 2 = 0 ∧ dcDNodes 16 = 0 := by
  constructor
  · norm_num [takagi_eighths, takagiEll_succ, takagiBit_eq,
      Nat.testBit_eq_decide_div_mod_eq, sum_range_succ]
  · rw [show 16 = 2 * (2 * 4) by decide, dcDNodes_two_mul (by decide),
      dcDNodes_two_mul (by decide), dcDNodes_small.2.2.1, mul_zero, mul_zero]

-- At k = 0, neither presentation reads a nonnegative bit position.
example : takagiNewdef 0 (-1) = 0 ∧ takagiNewdef 1 (-1) = 0 ∧
    dcDNodes 1 = 0 ∧ dcDNodes 2 = 0 := by
  have hbit (n i : ℕ) : takagiBit n (-1 - (i : ℤ)) = 0 := takagiBit_neg _ _ (by omega)
  simp [takagiNewdef_eq, takagiEll_succ, hbit, dcDNodes_one, dcDNodes_small.1]

-- Check that clients can apply the public theorem at an interior dyadic point.
example : takagiNewdef 3 ((3 : ℤ) - 1) = (dcDNodes (2 ^ 3 + 3) : ℝ) / 2 ^ 3 :=
  takagi_dyadic_eq_dcDNodes_div 3 3 (by decide)
