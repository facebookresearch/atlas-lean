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

example : mertens 10 = -1 := by
  rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, mertens_natCast]
  decide +kernel

example : mertens 5 = -2 := by
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, mertens_natCast]
  decide +kernel

-- The Mertens function is a step function of the real variable: `M(2.5) = M(2) = 0`.
example : mertens (5 / 2) = 0 := by
  rw [mertens_apply, show ⌊(5 / 2 : ℝ)⌋₊ = 2 by norm_num [Nat.floor_eq_iff]]
  decide +kernel

/-! ### Boundary values -/

example : mertens 1 = 1 := by
  rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, mertens_natCast]
  simp

example : mertens 0 = 0 := mertens_of_lt_one (by norm_num)
example : mertens (1 / 2) = 0 := mertens_of_lt_one (by norm_num)
example : mertens (-3) = 0 := mertens_of_lt_one (by norm_num)

example (x : ℝ) : |mertens x| ≤ ⌊x⌋₊ := abs_mertens_le x

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
