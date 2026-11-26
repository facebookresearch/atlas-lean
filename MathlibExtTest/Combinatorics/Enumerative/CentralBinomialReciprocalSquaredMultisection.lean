/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CentralBinomialReciprocalSquaredMultisection

open MetaMathlibExt

-- For m = 1 there is only the identity rotation.
example {x : ℂ} (hx : ‖x‖ < 4) :
    ∑' k : ℕ, x ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (1 * (k + 1))) =
      ∑' n : ℕ, x ^ (n + 1) / (((n + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (n + 1)) := by
  rw [tsum_div_sq_mul_centralBinom_mul_eq_multisection (m := 1) (by decide) (by simpa using hx)]
  simp

-- At zero there is no constant term for any positive m.
example {m : ℕ} (hm : 1 ≤ m) :
    ∑' k : ℕ, (0 : ℂ) ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (m * (k + 1))) = 0 := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [tsum_div_sq_mul_centralBinom_mul_eq_multisection hm (by simp)]
  simp [hmC]

-- The principal square root of -1 is I. The two rotations are I and -I and the factor is 2.
example :
    ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) / (((k + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (2 * (k + 1))) =
      2 * ((∑' n : ℕ, Complex.I ^ (n + 1) / (((n + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (n + 1))) +
        ∑' n : ℕ, (-Complex.I) ^ (n + 1) / (((n + 1 : ℕ) : ℂ) ^ 2 * Nat.centralBinom (n + 1))) := by
  have hz : (-1 : ℂ) ^ ((1 : ℂ) / 2) = Complex.I := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.log_neg_one]
    calc
      _ = Complex.exp (Real.pi / 2 * Complex.I) := by congr 1; ring
      _ = _ := Complex.exp_pi_div_two_mul_I
  have hw : Complex.exp (2 * Real.pi * Complex.I / 2) = -1 := by
    rw [← Complex.exp_pi_mul_I]
    congr 1
    ring
  rw [tsum_div_sq_mul_centralBinom_mul_eq_multisection (by decide : 1 ≤ 2) (by norm_num)]
  simp only [Nat.cast_ofNat, hz, hw, Finset.sum_range_succ]
  simp
