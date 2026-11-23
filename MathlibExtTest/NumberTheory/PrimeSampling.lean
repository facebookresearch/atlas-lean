/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeSampling
import Mathlib.Tactic.NormNum.Prime

/-! Tests for `MathlibExt.NumberTheory.PrimeSampling`. -/

namespace MathlibExtTest.PrimeSampling

open Nat

/-! Concrete dyadic intervals, enumerated by `decide`. -/

example : nBitPrimes 4 = {11, 13} := by decide
example : nBitPrimes 5 = {17, 19, 23, 29, 31} := by decide
example : (nBitPrimes 6).card = 7 := by decide

/-! The boundary cases: no `1`-bit prime, and `2` is the only power of two that is prime, so the
open-interval form fails exactly at `n = 2`. -/

example : nBitPrimes 1 = ∅ := nBitPrimes_one
example : nBitPrimes 2 = {2, 3} := by decide
example : (Finset.Ioo (2 ^ (2 - 1)) (2 ^ 2)).filter Nat.Prime = {3} := by decide
example : nBitPrimes 4 = (Finset.Ioo 8 16).filter Nat.Prime :=
  nBitPrimes_eq_filter_Ioo (by decide)

/-! Membership and the `Nat.size` characterization on a prime, a composite, and an out-of-range
prime. -/

example : 13 ∈ nBitPrimes 4 := mem_nBitPrimes.2 ⟨by norm_num, by norm_num, by norm_num⟩
example : 15 ∉ nBitPrimes 4 := fun h => absurd (mem_nBitPrimes.1 h).1 (by norm_num)
example : 17 ∉ nBitPrimes 4 := fun h => by have := (mem_nBitPrimes.1 h).2.2; norm_num at this
example : (13 : ℕ).size = 4 := (mem_nBitPrimes_iff_size.1 (by decide : 13 ∈ nBitPrimes 4)).2
example : 31 ∈ nBitPrimes 5 := mem_nBitPrimes_iff_size.2 ⟨by norm_num, by decide⟩

/-! Bertrand on a dyadic interval: the witness is an actual prime in range. -/

example : ∃ p, p.Prime ∧ 2 ^ 9 < p ∧ p < 2 ^ 10 :=
  exists_prime_Ioo_two_pow (n := 10) (by norm_num)
example : (nBitPrimes 64).Nonempty := nBitPrimes_nonempty (by norm_num)
example : 0 < (nBitPrimes 2048).card := card_nBitPrimes_pos (by norm_num)

/-! The uniform sampler on `(8, 16)`: two primes, each with probability `1/2`. -/

example : uniformNBitPrime 4 (by norm_num) 11 = 2⁻¹ := by
  rw [uniformNBitPrime_apply_of_mem _ (by decide)]
  rw [show (nBitPrimes 4).card = 2 by decide]
  norm_num

example : uniformNBitPrime 4 (by norm_num) 13 = 2⁻¹ := by
  rw [uniformNBitPrime_apply_of_mem _ (by decide), show (nBitPrimes 4).card = 2 by decide]
  norm_num

/-- The sampler is the shared `PMF.uniformFinset` on the `n`-bit primes. -/
example : uniformNBitPrime 4 (by norm_num) = PMF.uniformFinset {11, 13} (by decide) := by
  unfold uniformNBitPrime
  congr 1

example : uniformNBitPrime 4 (by norm_num) 12 = 0 :=
  uniformNBitPrime_apply_of_notMem _ (by decide)

example : uniformNBitPrime 4 (by norm_num) 17 = 0 :=
  uniformNBitPrime_apply_of_notMem _ (by decide)

/-- The sampler on `(16, 32)` puts mass `1/5` on each of its five primes. -/
example : uniformNBitPrime 5 (by norm_num) 23 = 5⁻¹ := by
  rw [uniformNBitPrime_apply_of_mem _ (by decide), show (nBitPrimes 5).card = 5 by decide]
  norm_num

example : 11 ∈ (uniformNBitPrime 4 (by norm_num)).support := by
  rw [support_uniformNBitPrime]; norm_num

example : 9 ∉ (uniformNBitPrime 4 (by norm_num)).support := by
  rw [support_uniformNBitPrime]; norm_num

example : (uniformNBitPrime 4 (by norm_num)).support = {p | p.Prime ∧ 8 < p ∧ p < 16} :=
  support_uniformNBitPrime_eq_Ioo (by norm_num)

example (p : ℕ) (hp : p ∈ (uniformNBitPrime 128 (by norm_num)).support) : p.Prime :=
  prime_of_mem_support_uniformNBitPrime _ hp

/-! The Chebyshev bound at `2 ^ 4 = 16`, where `π 16 = 6`. -/

example : (16 : ℕ).primeCounting = 6 := by decide

example : (2 : ℝ) ^ 4 * Real.log 2 - Real.log (2 ^ 4 + 1) ≤ 6 * (4 * Real.log 2) := by
  have h := primeCounting_two_pow_mul_log_ge 4
  rwa [show (2 ^ 4 : ℕ).primeCounting = 6 by decide] at h

/-! The probability form counts primes strictly below `2 ^ n`. At `n = 4` there are six
(`2, 3, 5, 7, 11, 13`), the same as `π 16`. At `n = 1` the two counts differ: `π 2 = 1` counts the
endpoint `2`, while no natural below `2` is prime, so the `2 ≤ n` hypothesis is needed. -/

example : (primesBelow (2 ^ 4)).card = 6 := by
  rw [card_primesBelow_two_pow (by norm_num)]; decide

example : (primesBelow (2 ^ 1)).card = 0 ∧ (2 ^ 1 : ℕ).primeCounting = 1 := by decide

example : (2 : ℝ) ^ 4 * Real.log 2 - Real.log (2 ^ 4 + 1) ≤ 6 * (4 * Real.log 2) := by
  have h := card_primesBelow_two_pow_mul_log_ge (n := 4) (by norm_num)
  rwa [show (primesBelow (2 ^ 4)).card = 6 by decide] at h

/-- At `n = 1` the left side of the bound is positive, so the bound with the strict count fails
there. -/
example : 0 < (2 : ℝ) ^ 1 * Real.log 2 - Real.log (2 ^ 1 + 1) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  norm_num
  linarith

/-! The `θ`-difference bound on `(8, 16]`, which holds two primes. -/

example : Chebyshev.theta ((2 : ℝ) ^ 4) - Chebyshev.theta ((2 : ℝ) ^ (4 - 1)) ≤
    2 * (4 * Real.log 2) := by
  have h := theta_sub_theta_le_card_nBitPrimes_mul (n := 4) (by norm_num)
  rwa [show (nBitPrimes 4).card = 2 by decide, Nat.cast_ofNat] at h

/-! The explicit density bound instantiated at an RSA-size width. -/

example : 0 < (nBitPrimes 1024).card := card_nBitPrimes_pos (by norm_num)

example := card_nBitPrimes_mul_log_gt (n := 1024) (by norm_num)

end MathlibExtTest.PrimeSampling
