/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.DivisorBounds

/-!
# Tests for divisor bounds
-/

@[expose] public section

open Filter Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega

-- `d(n) ≤ C n^ε` at `ε = 1/2`, applied at `n = 0` (where `d(0) = 0`).
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (σ 0 n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 : ℝ) :=
  exists_sigma_zero_le_mul_rpow (by norm_num)

example : (fun n : ℕ => (σ 0 n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) :=
  sigma_zero_isLittleO_rpow (by norm_num)

example : ∀ᶠ n : ℕ in atTop,
    (σ 0 n : ℝ) < (2 : ℝ) ^ ((1 + 1) * Real.log n / Real.log (Real.log n)) :=
  eventually_sigma_zero_lt_two_rpow one_pos

example : (fun n : ℕ => (ω n : ℝ)) =O[atTop] fun n : ℕ => Real.log n / Real.log (Real.log n) :=
  cardDistinctFactors_isBigO_log_div_log_log

-- The explicit Ramanujan–Wigert lemma at `n = 1`, `ε = 1`, `y = 2`, `B = 1`: `d(1) ≤ 1`.
example : (σ 0 1 : ℝ) ≤ 1 ^ ⌈(2 : ℝ)⌉₊ * ((1 : ℕ) : ℝ) ^ (1 : ℝ) :=
  sigma_zero_le_pow_ceil_mul_rpow one_ne_zero zero_le_one (by norm_num) (by norm_num) le_rfl
    (by simp)
