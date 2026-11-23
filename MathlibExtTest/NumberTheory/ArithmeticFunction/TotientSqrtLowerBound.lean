/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.TotientSqrtLowerBound

/-! # Tests for `MathlibExt.NumberTheory.ArithmeticFunction.TotientSqrtLowerBound` -/

namespace MathlibExtTest.TotientSqrtLowerBound

open MetaMathlibExt

-- At `n = 1` the bound reads `√1 / 2 ≤ φ 1 = 1`.
example : Real.sqrt 1 / 2 ≤ 1 := by
  simpa using sqrt_div_two_le_totient 1 one_pos

-- Squaring both sides gives the bound `n ≤ 4 φ(n)²` in `ℕ`.
example (n : ℕ) (hn : 0 < n) : n ≤ 4 * Nat.totient n ^ 2 := by
  have h : Real.sqrt n ≤ 2 * Nat.totient n := by
    linarith [sqrt_div_two_le_totient n hn]
  rw [Real.sqrt_le_left (by positivity)] at h
  exact_mod_cast (by linarith : (n : ℝ) ≤ 4 * (Nat.totient n : ℝ) ^ 2)

-- Since `φ n` is an integer, `√n / 2 > 1` forces `φ n ≥ 2`; this happens for `n ≥ 5`.
example (n : ℕ) (hn : 5 ≤ n) : 2 ≤ Nat.totient n := by
  have h := sqrt_div_two_le_totient n (by omega)
  have h2 : (2 : ℝ) < Real.sqrt n := by
    rw [Real.lt_sqrt zero_le_two]
    exact_mod_cast (by omega : 4 < n)
  have h1 : (1 : ℝ) < Nat.totient n := by linarith
  exact_mod_cast h1

-- The constant `1 / 2` cannot be replaced by `1`: `φ 2 = 1 < √2`.
example : ¬ Real.sqrt 2 ≤ (Nat.totient 2 : ℝ) := by
  rw [Nat.totient_two, Nat.cast_one, not_le, Real.lt_sqrt zero_le_one]
  norm_num

end MathlibExtTest.TotientSqrtLowerBound
