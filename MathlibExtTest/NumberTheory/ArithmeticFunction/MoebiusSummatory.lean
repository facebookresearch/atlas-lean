/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusSummatory

/-!
# Tests for the Mertens function and summatory Möbius inversion
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-! ### Concrete values -/

example : M 10 = -1 := by
  rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, M_natCast]
  exact_mod_cast (by decide +kernel : ∑ n ∈ Finset.Icc 1 10, μ n = -1)

example : M 5 = -2 := by
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, M_natCast]
  exact_mod_cast (by decide +kernel : ∑ n ∈ Finset.Icc 1 5, μ n = -2)

-- The Mertens function is a step function of the real variable: `M(2.5) = M(2) = 0`.
example : M (5 / 2) = 0 := by
  rw [M_eq_sum_Icc, show ⌊(5 / 2 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
  exact_mod_cast (by decide +kernel : ∑ n ∈ Finset.Icc 1 2, μ n = 0)

/-! ### Boundary values -/

example : M 1 = 1 := by
  rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, M_natCast]
  simp

example : M 0 = 0 := M_of_lt_one (by norm_num)
example : M (1 / 2) = 0 := M_of_lt_one (by norm_num)
example : M (-3) = 0 := M_of_lt_one (by norm_num)

example (x : ℝ) : |M x| ≤ ⌊x⌋₊ := abs_M_le x

/-! ### Möbius inversion for summatory functions -/

-- Summatory inversion with `F = 1` on `[1, ∞)`: `G(x) = ⌊x⌋` and `∑_{n ≤ x} μ(n) ⌊x / n⌋ = 1`.
example (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, μ n • ((⌊x / n⌋₊ : ℕ) : ℤ) = 1 := by
  have h := (sum_floor_div_eq_iff_sum_moebius_smul_floor_div_eq (A := ℤ)
    (fun _ => 1) (fun y => ((⌊y⌋₊ : ℕ) : ℤ))).mp (fun y hy => by simp) x hx
  exact h.symm

-- The hyperbola reindexing at `N = 4` with `f n m = n`.
example : ∑ n ∈ Icc 1 4, ∑ _m ∈ Icc 1 (4 / n), n = ∑ r ∈ Icc 1 4, ∑ d ∈ r.divisors, d :=
  Nat.sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors 4 fun n _ => n
