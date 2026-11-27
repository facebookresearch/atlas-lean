/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CentralBinomialReciprocalMultisection

open MetaMathlibExt

-- At zero all rotations coincide, and the constant term survives for every positive m.
example (m : ℕ) (hm : 1 ≤ m) :
    ∑' k : ℕ, (0 : ℂ) ^ k / (Nat.centralBinom (m * k) : ℂ) = 1 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hsum : ∑' n : ℕ, (0 : ℂ) ^ n / (Nat.centralBinom n : ℂ) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  rw [tsum_div_centralBinom_mul_eq_multisection hm (by simp)]
  simp [hsum, hm0]

-- The principal square root of -1 is I, so bisection averages the series at I and -I.
example :
    ∑' k : ℕ, (-1 : ℂ) ^ k / (Nat.centralBinom (2 * k) : ℂ) =
      (1 / 2 : ℂ) * ((∑' n : ℕ, Complex.I ^ n / (Nat.centralBinom n : ℂ)) +
        ∑' n : ℕ, (-Complex.I) ^ n / (Nat.centralBinom n : ℂ)) := by
  have hz : (-1 : ℂ) ^ ((1 : ℂ) / 2) = Complex.I := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.log_neg_one]
    calc
      _ = Complex.exp (Real.pi / 2 * Complex.I) := by congr 1; ring
      _ = _ := Complex.exp_pi_div_two_mul_I
  have hw : Complex.exp (2 * Real.pi * Complex.I / 2) = -1 := by
    rw [← Complex.exp_pi_mul_I]
    congr 1
    ring
  rw [tsum_div_centralBinom_mul_eq_multisection (by decide : 1 ≤ 2) (by norm_num)]
  simp only [Nat.cast_ofNat, hz, hw, Finset.sum_range_succ]
  simp
