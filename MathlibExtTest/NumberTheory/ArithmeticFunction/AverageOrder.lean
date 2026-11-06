/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.AverageOrder

/-!
# Tests for average orders of arithmetic functions
-/

@[expose] public section

open Finset Filter Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma

/-! ### Convolution identities -/

example : ((μ : ArithmeticFunction ℝ) * (ArithmeticFunction.id : ArithmeticFunction ℝ)) 12 = 4 := by
  rw [coe_moebius_mul_coe_id_apply]; norm_num [show Nat.totient 12 = 4 by decide]

example : ((ζ : ArithmeticFunction ℝ) * (ArithmeticFunction.id : ArithmeticFunction ℝ)) 6 = 12 := by
  rw [coe_zeta_mul_coe_id_apply, show σ 1 6 = 12 by decide]; norm_num

example : (pdiv (μ : ArithmeticFunction ℝ) (ArithmeticFunction.id : ArithmeticFunction ℝ) *
    (ζ : ArithmeticFunction ℝ)) 0 = 0 := by simp

/-! ### Explicit bounds at small arguments -/

-- `g = δ` (the Dirichlet unit) in the `id`-convolution bound: `∑_{n ≤ N} n - N² / 2 = N / 2`.
example (N : ℕ) :
    |∑ n ∈ Ioc 0 N, ((1 : ArithmeticFunction ℝ) * ArithmeticFunction.id) n
        - (∑' d, (1 : ArithmeticFunction ℝ) d / (d : ℝ) ^ 2) / 2 * (N : ℝ) ^ 2|
      ≤ (N : ℝ) / 2 * (1 + Real.log N) + N :=
  abs_sum_Ioc_mul_id_sub_le 1 (fun n => by
    rcases eq_or_ne n 1 with rfl | h <;> simp [one_apply_ne, *]) N

-- Boundary `N = 0` of the `ζ`-convolution bound: `0 ≤ 3`.
example (g : ArithmeticFunction ℝ) (hg : ∀ n, |g n| ≤ 1 / n) :
    |∑ n ∈ Ioc 0 0, (g * (ζ : ArithmeticFunction ℝ)) n - (∑' d, g d / d) * (0 : ℕ)| ≤
      3 + Real.log (0 : ℕ) :=
  abs_sum_Ioc_mul_zeta_sub_le g hg 0

-- Dirichlet's divisor problem bound at `x = 1`: `|1 - 0| ≤ 1` is sharp.
example : |∑ n ∈ Ioc 0 ⌊(1 : ℝ)⌋₊, (σ 0 n : ℝ) - 1 * Real.log 1| = 1 := by simp
example : |∑ n ∈ Ioc 0 ⌊(1 : ℝ)⌋₊, (σ 0 n : ℝ) - 1 * Real.log 1| ≤ 1 :=
  abs_sum_sigma_zero_sub_mul_log_le le_rfl

example : |∑ n ∈ Ioc 0 ⌊(1 : ℝ)⌋₊, (n.totient : ℝ) / n - 6 / Real.pi ^ 2 * 1| ≤ Real.log 1 + 5 :=
  Nat.abs_sum_totient_div_sub_le le_rfl

-- Coprime sums with `k = 1` reduce to `∑_{n ≤ x} n`.
example (x : ℝ) (hx : 0 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Coprime 1, (n : ℝ) - ((1 : ℕ).totient : ℝ) / (2 * ((1 : ℕ) : ℝ)) * x ^ 2|
      ≤ 2 * #(1 : ℕ).divisors * x :=
  Nat.abs_sum_coprime_sub_totient_div_mul_sq_le one_ne_zero hx

/-! ### Asymptotics -/

example : (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (n.totient : ℝ)) ~[atTop]
    fun x => 3 / Real.pi ^ 2 * x ^ 2 :=
  Nat.sum_totient_isEquivalent

example : (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 1 n : ℝ)) ~[atTop]
    fun x => Real.pi ^ 2 / 12 * x ^ 2 :=
  sum_sigma_one_isEquivalent

example : (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, 1 / (n.totient : ℝ)) =O[atTop] fun x : ℝ => Real.log x :=
  Nat.sum_one_div_totient_isBigO_log
