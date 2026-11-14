/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Sieve.Legendre
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Tests for Legendre's sieve
-/

@[expose] public section

open Nat Finset Filter
open scoped ArithmeticFunction.Moebius

/-! ### Concrete values of `Φ(N, k)` -/

-- `primorial 1 = 1`: nothing is sifted out.
example : roughCount 10 1 = 10 := by decide
-- Odd numbers up to `10`.
example : roughCount 10 2 = 5 := by decide
-- Integers up to `30` coprime to `30`: `φ(30) = 8`.
example : roughCount 30 5 = 8 := by decide
example : roughCount 30 5 = Nat.totient 30 := by decide
-- `1` is `k`-rough for every `k`.
example : roughCount 1 100 = 1 := by decide

/-! ### Boundary values -/

example (k : ℕ) : roughCount 0 k = 0 := by simp [roughCount]
example (N : ℕ) : roughCount N 0 = N := by simp [roughCount]
example (N : ℕ) : roughCount N 1 = N := by
  simp [roughCount, show primorial 1 = 1 by decide]

/-! ### Agreement with `Nat.IsRough` and Legendre's identity -/

example : (7 : ℕ).IsRough 5 := isRough_iff_coprime_primorial.mpr ⟨by norm_num, by decide⟩
example : ¬ (0 : ℕ).IsRough 5 := fun h => by
  simpa using (isRough_iff_coprime_primorial.mp h).1
example : ¬ (9 : ℕ).IsRough 5 := fun h => by
  have := (isRough_iff_coprime_primorial.mp h).2
  revert this; decide

example : roughCount 10 3 = {n | n ≤ 10 ∧ n.IsRough 3}.ncard := roughCount_eq_ncard 10 3

example : (roughCount 30 5 : ℤ) = ∑ d ∈ (primorial 5).divisors, μ d * ((30 / d : ℕ) : ℤ) :=
  roughCount_eq_sum_moebius_mul_div 30 5

example : ((#{n ∈ Icc 1 12 | n.Coprime 6} : ℕ) : ℤ) = 4 := by
  rw [card_filter_coprime_eq_sum_moebius_mul_div (by norm_num)]
  decide +kernel

/-! ### Asymptotic statements -/

example : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ z : ℝ, 3 ≤ z →
    |(roughCount ⌊x⌋₊ ⌊z⌋₊ : ℝ) - x * ∏ p ∈ primesLE ⌊z⌋₊, (1 - (p : ℝ)⁻¹)| ≤
      C * x * Real.log z * Real.exp (-(Real.log x / Real.log z)) :=
  abs_roughCount_sub_mul_prod_le

example : Asymptotics.IsEquivalent atTop
    (fun x : ℝ => (roughCount ⌊x⌋₊ ⌊Real.log x ^ (2 : ℝ)⌋₊ : ℝ))
    (fun x : ℝ => x * Real.exp (-Real.eulerMascheroniConstant) /
      (2 * Real.log (Real.log x))) :=
  roughCount_log_rpow_isEquivalent (by norm_num)

-- The divergence hypothesis of the density-zero theorem is met by the set of all primes.
open Classical in
example : (fun x : ℝ => ((#{n ∈ Icc 1 ⌊x⌋₊ | ∀ p ∈ {p : ℕ | p.Prime}, ¬ p ∣ n} : ℕ) : ℝ))
    =o[atTop] (fun x => x) :=
  card_filter_forall_not_dvd_isLittleO _ (fun _ hp => hp) not_summable_one_div_on_primes
