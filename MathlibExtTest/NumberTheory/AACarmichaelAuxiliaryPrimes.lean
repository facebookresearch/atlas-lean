/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Simproc.Factors
import MathlibExt.NumberTheory.AACarmichaelAuxiliaryPrimes

open Finset Filter MetaMathlibExt Real

-- At z = 10 the prime 5 lies exactly at the lower endpoint, and 2 * (5 * 7) + 1 = 71.
example :
    2 ≤ log 10 ∧
      35 ∣ ∏ r ∈ (Iic 10).filter (fun r : ℕ => r.Prime ∧ (10 : ℝ) / 2 ≤ r), r ∧
      (35 : ℕ).primeFactors.card = ⌊log 10⌋₊ ∧ Nat.Prime (35 * 2 + 1) := by
  have hlog : 2 ≤ log 10 ∧ log 10 < 3 := by
    rw [log_ten_eq]
    constructor
    · linarith [log_two_gt_d9, log_five_gt_d9]
    · linarith [log_two_lt_d9, log_five_lt_d9]
  refine ⟨hlog.1, ?_, ?_, by decide⟩
  · have hhalf (r : ℕ) : (10 : ℝ) / 2 ≤ r ↔ 5 ≤ r := by norm_num
    simp_rw [hhalf]
    decide
  · have hfloor : ⌊log 10⌋₊ = 2 := (Nat.floor_eq_iff' (by decide)).mpr (by norm_num; exact hlog)
    rw [hfloor, ← Nat.toFinset_factors]
    simp only [Nat.primeFactorsList_ofNat]
    decide

-- With A = 1/2 and j = 2, a chosen subset of interval primes gives the divisor directly.
example :
    ∀ᶠ z : ℕ in atTop, ∀ s : Finset ℕ,
      s ⊆ (Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r) →
      s.card = ⌊log z⌋₊ → (s.prod id * 2 + 1).Prime →
      (↑(s.prod id * 2 + 1) : ℝ) ∈
        Set.Icc (((z : ℝ) / 6) ^ log z) (2 * (z : ℝ) ^ log z * log z) := by
  filter_upwards [rpow_log_le_prime_of_eq_mul_add_one_of_dvd_prod_primes (1 / 2),
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2] with z hz hlog
  intro s hs hcard hprime
  have hfac : (s.prod id).primeFactors = s :=
    Nat.primeFactors_prod (fun r hr => (mem_filter.mp (hs hr)).2.1)
  have h := hz 2 (s.prod id) _ (by decide) (by simpa using hlog)
    (prod_dvd_prod_of_subset _ _ id hs) (by rwa [hfac]) hprime rfl
  simpa using h
