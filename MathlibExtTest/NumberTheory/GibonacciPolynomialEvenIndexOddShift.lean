/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialEvenIndexOddShift
import Mathlib.Tactic.NormNum

/-! # Tests for odd-shift telescoping at even Gibonacci indices -/

open MetaMathlibExt Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- The smallest odd shift keeps just the Fibonacci term of index 2, which evaluates to 2.
example : ∑' n : ℕ, (1 / aeval (2 : ℝ) (𝔣 (2 * n + 2)) ^ 1 -
    1 / aeval (2 : ℝ) (𝔣 (2 * n + 2 + 2)) ^ 1) = 1 / 2 := by
  have h := tsum_inv_pow_gibonacciPoly_succ_sub_odd (x := 2) (by norm_num) (g := 𝔣)
    (Or.inl rfl) (k := 1) (by decide) (lam := 1) (by decide)
  exact h.trans (by norm_num [generalizedFibonacciPolynomial])

-- A shift of three keeps the Lucas terms at 2, 4 and 6, which evaluate to 3, 7 and 18.
example : ∑' n : ℕ, (1 / aeval (1 : ℝ) (𝔩 (2 * n + 2)) ^ 2 -
    1 / aeval (1 : ℝ) (𝔩 (2 * n + 2 + 6)) ^ 2) = 1 / 9 + 1 / 49 + 1 / 324 := by
  have h := tsum_inv_pow_gibonacciPoly_succ_sub_odd (x := 1) (by norm_num) (g := 𝔩)
    (Or.inr rfl) (k := 3) (by decide) (lam := 2) (by decide)
  have hIcc : Finset.Icc 1 (3 : ℕ) = {1, 2, 3} := by decide
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial, map_ofNat])
