/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.TakagiDyadicSlope

/-! # Tests for the Hamming weight formula from consecutive Takagi values -/

open Finset MetaMathlibExt

-- Evaluate the two-bit presentations directly from the public series, not the slope formula.
private theorem takagi_quarters (n : ℕ) :
    takagiNewdef n 1 =
      ((takagiEll n 1 2 : ℝ) + ((takagiBit n 1 + takagiBit n 0 : ℕ) : ℝ)) / 4 := by
  have hprefix (i : ℕ) :
      (∑ j ∈ range (i + 2), takagiBit n (1 - (j : ℤ))) = takagiBit n 1 + takagiBit n 0 := by
    induction i with
    | zero => simp [sum_range_succ]
    | succ i ih =>
      have hneg : (1 : ℤ) - (↑(i + 2) : ℤ) < 0 := by omega
      rw [show i + 1 + 2 = (i + 2) + 1 by omega, sum_range_succ, ih,
        takagiBit_neg _ _ hneg, add_zero]
  let f (i : ℕ) : ℝ := (takagiEll n 1 (i + 1) : ℝ) / 2 ^ (i + 1)
  have htail (i : ℕ) : f (i + 2) =
      (((takagiBit n 1 + takagiBit n 0 : ℕ) : ℝ) / 4) / 2 / 2 ^ i := by
    have hneg : (1 : ℤ) - (↑(i + 2) : ℤ) < 0 := by omega
    dsimp only [f]
    rw [takagiEll_succ, takagiBit_neg _ _ hneg, ite_eq_left rfl, hprefix,
      show i + 2 + 1 = 3 + i by omega, pow_add, div_div, div_div, ← mul_assoc]
    norm_num
  have hs : Summable f := (summable_nat_add_iff 2).mp <|
    (summable_geometric_two' _).congr fun i => (htail i).symm
  rw [takagiNewdef_eq]
  change (∑' i, f i) = _
  rw [← hs.sum_add_tsum_nat_add 2]
  simp_rw [htail, tsum_geometric_two']
  norm_num [sum_range_succ, f, takagiEll_one, add_div]

-- The rise, flat step, and right-endpoint fall at quarter spacing. Check both the actual
-- Takagi values and the resulting identity against independently computed digit sums.
example :
    takagiNewdef 0 1 = 0 ∧ takagiNewdef 1 1 = 1 / 2 ∧ takagiNewdef 2 1 = 1 / 2 ∧
      takagiNewdef 3 1 = 1 / 2 ∧ takagiNewdef 4 1 = 0 := by
  norm_num [takagi_quarters, takagiEll_succ, takagiBit_eq, Nat.testBit_eq_decide_div_mod_eq,
    sum_range_succ]

example :
    ((Nat.digits 2 4).sum : ℝ) = 2 * (takagiNewdef 0 1 - takagiNewdef 1 1) + 2 ∧
      ((Nat.digits 2 5).sum : ℝ) = 2 * (takagiNewdef 1 1 - takagiNewdef 2 1) + 2 ∧
      ((Nat.digits 2 7).sum : ℝ) = 2 * (takagiNewdef 3 1 - takagiNewdef 4 1) + 2 := by
  have h4 : (Nat.digits 2 4).sum = 1 := by decide
  have h5 : (Nat.digits 2 5).sum = 2 := by decide
  have h7 : (Nat.digits 2 7).sum = 3 := by decide
  norm_num [h4, h5, h7, takagi_quarters, takagiEll_succ, takagiBit_eq,
    Nat.testBit_eq_decide_div_mod_eq, sum_range_succ]

-- At k = 0 both presentations have no nonnegative bit positions in their series.
example :
    ((Nat.digits 2 1).sum : ℝ) = (1 / 2) * (takagiNewdef 0 (-1) - takagiNewdef 1 (-1)) + 1 := by
  have h (n i : ℕ) : takagiBit n (-1 - (i : ℤ)) = 0 := takagiBit_neg _ _ (by omega)
  have hw : (Nat.digits 2 1).sum = 1 := by decide
  norm_num [takagiNewdef_eq, takagiEll_succ, h, hw]

-- A client can apply the public theorem at the last interval of the mesh.
example :
    ((Nat.digits 2 (2 ^ 2 + 3)).sum : ℝ) =
      2 ^ 2 / 2 * (takagiNewdef 3 ((2 : ℤ) - 1) - takagiNewdef (3 + 1) ((2 : ℤ) - 1)) +
        ((2 : ℝ) + 2) / 2 :=
  hammingWeight_eq_takagi_diff 2 3 (by decide)
