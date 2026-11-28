/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RemainderSetBoundsPrimeCounting
import MathlibExt.NumberTheory.PrimeCounting.ExplicitPrimeEstimates
import Mathlib.Analysis.Complex.ExponentialBounds

open MetaMathlibExt ExplicitPrimeEstimates Real

-- Check the public signature separately from the independent numerical cases.
example {n : ℕ} (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ 13 / 10 * n / log n :=
  primeCounting_le_thirteen_tenths hn

-- At the lower endpoint, exactly one prime contributes.
example : (Nat.primeCounting 2 : ℝ) ≤ 13 / 10 * 2 / log 2 := by
  rw [show Nat.primeCounting 2 = 1 by decide, Nat.cast_one, le_div_iff₀ (log_pos one_lt_two)]
  linarith [log_two_lt_d9]

-- The finite range includes 113 itself; bound its logarithm by log 128.
set_option maxRecDepth 4096 in
example : (Nat.primeCounting 113 : ℝ) ≤ 13 / 10 * 113 / log 113 := by
  have hlog := log_le_log (by norm_num : (0 : ℝ) < 113) (by norm_num : (113 : ℝ) ≤ 2 ^ 7)
  rw [log_pow] at hlog
  norm_num at hlog
  rw [show Nat.primeCounting 113 = 30 by decide +kernel, Nat.cast_ofNat,
    le_div_iff₀ (log_pos (by norm_num))]
  linarith [log_two_lt_d9]

-- The indicator checks both primes and composites, including above its gcd cutoff.
example : primeFlag 361 = 0 ∧ primeFlag 367 = 1 ∧ primeFlag 529 = 0 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
-- Kernel-check the prime count immediately before the analytic cutoff.
private lemma primeCounting_before_cutoff : Nat.primeCounting 65535 = 6542 := by
  rw [primeCounting_eq_countP_primeFlag (by decide)]
  decide +kernel

private lemma log_le_cutoff {x : ℝ} (hx : 0 < x) (hle : x ≤ 65536) : log x ≤ 16 * log 2 := by
  have h := log_le_log hx hle
  rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow] at h
  simpa only [Nat.cast_ofNat] using h

-- Independently verify the claimed inequality on both sides of the branch boundary.
example : (Nat.primeCounting 65535 : ℝ) ≤ 13 / 10 * 65535 / log 65535 := by
  have hlog := log_le_cutoff (by norm_num : (0 : ℝ) < 65535) (by norm_num)
  rw [primeCounting_before_cutoff, Nat.cast_ofNat, le_div_iff₀ (log_pos (by norm_num))]
  linarith [log_two_lt_d9]

example : (Nat.primeCounting 65536 : ℝ) ≤ 13 / 10 * 65536 / log 65536 := by
  have hcomposite : ¬ Nat.Prime 65536 := by
    rw [show (65536 : ℕ) = 256 * 256 by decide]
    exact Nat.not_prime_mul (by decide) (by decide)
  have hcount : Nat.primeCounting 65536 = Nat.primeCounting 65535 := by
    simpa only [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting'] using
      Nat.count_succ_eq_count hcomposite
  have hlog := log_le_cutoff (by norm_num : (0 : ℝ) < 65536) le_rfl
  rw [hcount, primeCounting_before_cutoff, Nat.cast_ofNat,
    le_div_iff₀ (log_pos (by norm_num))]
  linarith [log_two_lt_d9]
