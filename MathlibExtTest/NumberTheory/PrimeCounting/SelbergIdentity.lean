/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.SelbergIdentity

/-!
# Tests for Selberg's identity
-/

@[expose] public section

open Finset Filter Asymptotics Chebyshev
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

/-! ### Concrete and boundary values of Selberg's sum -/

example : selbergSum 1 = 0 := by simp [selbergSum]
example : selbergSum (1 / 2) = 0 := by
  rw [selbergSum, Nat.floor_eq_zero.mpr (by norm_num)]; simp
example : selbergSum (-5) = 0 := by
  rw [selbergSum, Nat.floor_eq_zero.mpr (by norm_num)]; simp

-- `S(2) = log² 2 + (log² 2 + μ(2) log² 1) = 2 log² 2`.
example : selbergSum 2 = 2 * Real.log 2 ^ 2 := by
  rw [selbergSum, show ⌊(2 : ℝ)⌋₊ = 2 by norm_num, show Ioc 0 2 = {1, 2} by rfl,
    sum_pair (by norm_num), Nat.Prime.sum_divisors Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  simp
  ring

/-! ### Main statements -/

-- Selberg's identity: `∑_{n ≤ x} Λ(n) log n + ∑_{mn ≤ x} Λ(m) Λ(n) = 2 x log x + O(x)`.
example : (fun x : ℝ => ψ x * Real.log x + ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ψ (x / n) - 2 * x * Real.log x)
    =O[atTop] fun x : ℝ => x :=
  psi_mul_log_add_sum_vonMangoldt_mul_psi_sub_isBigO

example : (fun x : ℝ => selbergSum x - 2 * x * Real.log x) =O[atTop] fun x : ℝ => x :=
  selbergSum_sub_two_mul_mul_log_isBigO

-- `k = 0` of the auxiliary estimate is `⌊x⌋ = O(x)`.
example : (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (x / n) ^ 0) =O[atTop] fun x : ℝ => x :=
  Real.sum_log_div_pow_isBigO 0
