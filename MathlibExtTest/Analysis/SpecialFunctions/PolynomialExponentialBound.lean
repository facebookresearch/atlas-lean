/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.SpecialFunctions.PolynomialExponentialBound
import Mathlib.Tactic.NormNum

-- A concrete coefficient: 2! / 1^2 has natural ceiling 2.
example (x : ℝ) (hx : 0 ≤ x) : x ^ 2 ≤ 2 * Real.exp x := by
  have h := Real.pow_le_natCeil_mul_exp 2 (by norm_num : (0 : ℝ) < 1) hx
  simpa using h

-- Degree zero and zero input retain the 0^0 = 1 boundary.
example : (0 : ℝ) ^ 0 ≤
    (⌈(Nat.factorial 0 : ℝ) / (1 : ℝ) ^ 0⌉₊ : ℝ) * Real.exp (1 * 0) :=
  Real.pow_le_natCeil_mul_exp 0 (by norm_num) (by norm_num)

example {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) : 1 ≤ Real.exp (c * x) := by
  have h := Real.pow_le_natCeil_mul_exp 0 hc hx
  simpa using h

-- The constant is chosen once and works for every nonnegative real input.
example {c : ℝ} (hc : 0 < c) :
    ∃ C : ℕ, ∀ x : ℝ, 0 ≤ x → x ^ 3 ≤ C * Real.exp (c * x) :=
  Real.exists_nat_pow_le_mul_exp 3 hc

-- The source theorem uses all natural inputs and a base-two exponential.
example {c : ℝ} (hc : 0 < c) :
    ∃ C : ℕ, ∀ x : ℕ, (x : ℝ) ^ 4 ≤ C * (2 : ℝ) ^ (c * x) :=
  Real.exists_nat_pow_le_mul_two_rpow 4 hc

#print axioms Real.pow_le_natCeil_mul_exp
#print axioms Real.exists_nat_pow_le_mul_exp
#print axioms Real.exists_nat_pow_le_mul_two_rpow
