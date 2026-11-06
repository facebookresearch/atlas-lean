/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.NairIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Tests for Nair's integral
-/

@[expose] public section

open scoped Chebyshev

example : Nat.lcmUpto 3 = 6 := by decide

-- `n = 1`: `lcm(1, 2, 3) ∫₀¹ x (1 - x) dx = 6 / 6 = 1`.
example : (Nat.lcmUpto (2 * 1 + 1) : ℝ) * ∫ x in (0 : ℝ)..1, x ^ 1 * (1 - x) ^ 1 = 1 := by
  rw [show Nat.lcmUpto (2 * 1 + 1) = 6 by decide]
  have : ∫ x in (0 : ℝ)..1, x ^ 1 * (1 - x) ^ 1 = 1 / 6 := by
    simp only [pow_one, mul_sub, mul_one]
    rw [intervalIntegral.integral_sub (f := fun x => x) (g := fun x => x * x)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [← sq, integral_pow, integral_id]
    norm_num
  rw [this]; norm_num

-- `n = 0`: the integral is `1` and `lcm(1) = 1`.
example : (Nat.lcmUpto (2 * 0 + 1) : ℝ) * ∫ x in (0 : ℝ)..1, x ^ 0 * (1 - x) ^ 0 = 1 := by
  rw [show Nat.lcmUpto (2 * 0 + 1) = 1 by decide]
  simp

example (n : ℕ) : ∃ m : ℕ, 0 < m ∧
    (Nat.lcmUpto (2 * n + 1) : ℝ) * ∫ x in (0 : ℝ)..1, x ^ n * (1 - x) ^ n = m :=
  Nat.exists_pos_eq_lcmUpto_mul_integral n

-- As a consequence, `e^{ψ(2n+1)} ≥ 1 / ∫₀¹ xⁿ(1 - x)ⁿ`; at `n = 3` the integral is `1/140`.
example : ∃ m : ℕ, 0 < m ∧
    Real.exp (ψ (2 * 3 + 1)) * ∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ 3 = m :=
  Chebyshev.exists_pos_eq_exp_psi_mul_integral 3
