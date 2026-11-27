/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.KFullPowerFreeParity

open Filter Topology

-- Only the exponent 2 is allowed at the prime 2, so the ratio tends to 2.
example :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull 2 n ∧ n.IsPowerFree 3 ∧ Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull 2 n ∧ n.IsPowerFree 3 ∧ Even n}.ncard)
      atTop (𝓝 2) := by
  have h := MetaMathlibExt.tendsto_card_odd_kFull_lFree_div_card_even_kFull_lFree
    (k := 2) (l := 3) le_rfl (by decide)
  norm_num only [Nat.cast_ofNat] at h
  have hp : (2 : ℝ) ^ (1 / 2 : ℝ) = 2 * (2 : ℝ) ^ (-(1 / 2) : ℝ) := by
    calc
      _ = (2 : ℝ) ^ ((1 : ℝ) + -(1 / 2)) :=
        congrArg (fun t : ℝ => (2 : ℝ) ^ t) (by norm_num)
      _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hd : 1 - (2 : ℝ) ^ (-(1 / 2) : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)).ne'
  rw [hp, ← mul_one_sub, mul_div_cancel_right₀ _ hd] at h
  exact h

-- Both exponents 2 and 3 are allowed at the prime 2.
example :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull 2 n ∧ n.IsPowerFree 4 ∧ Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull 2 n ∧ n.IsPowerFree 4 ∧ Even n}.ncard)
      atTop (𝓝 ((2 - Real.sqrt 2) / (1 / 2))) := by
  have h := MetaMathlibExt.tendsto_card_odd_kFull_lFree_div_card_even_kFull_lFree
    (k := 2) (l := 4) le_rfl (by decide)
  norm_num only [Nat.cast_ofNat] at h
  simpa only [Real.sqrt_eq_rpow] using h
