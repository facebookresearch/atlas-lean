/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialPowerSums
import Mathlib.Tactic.NormNum

open MetaMathlibExt Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- At x = 1 the three surviving Fibonacci numbers are 1, 2, and 5.
example : ∑' n : ℕ, (1 / aeval (1 : ℝ) (𝔣 (2 * n + 1)) -
    1 / aeval (1 : ℝ) (𝔣 (2 * n + 1 + 6))) = 17 / 10 := by
  have h := tsum_inv_pow_gibonacciPoly_sub_odd (x := 1) (by norm_num) (g := 𝔣)
    (Or.inl rfl) (k := 3) (by decide) (lam := 1) (by decide)
  have hIcc : Finset.Icc 1 (3 : ℕ) = {1, 2, 3} := by decide
  simp only [pow_one] at h
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial])

-- With the smallest shift, only the first Lucas polynomial survives, even for 0 < x < 1.
example : ∑' n : ℕ, (1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 1)) ^ 2 -
    1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 1 + 2)) ^ 2) = 4 := by
  have h := tsum_inv_pow_gibonacciPoly_sub_odd (x := 1 / 2) (by norm_num) (g := 𝔩)
    (Or.inr rfl) (k := 1) (by decide) (lam := 2) (by decide)
  exact h.trans (by norm_num)
