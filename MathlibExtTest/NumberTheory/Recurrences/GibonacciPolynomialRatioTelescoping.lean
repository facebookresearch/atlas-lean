/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialRatioTelescoping

/-! # Fibonacci and Lucas polynomial ratio sums at `x = 3/2` -/

namespace MetaMathlibExt.hasSum_gibonacciPoly_pow_ratio_telescoping

open Polynomial

local notation "F" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

private theorem sqrt_discriminant : √((3 / 2 : ℝ) ^ 2 + 4) = 5 / 2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

-- The boundary t = 2p starts at F₂, with both the shift and the power equal to two.
example : HasSum (fun n : ℕ =>
    (F (2 * n + 2 + 2) / F (2 * n + 2)) ^ 2 -
      (F (2 * n + 4 + 2) / F (2 * n + 4)) ^ 2) (33 / 16 : ℝ) := by
  have h := hasSum_gibonacciPoly_pow_ratio_telescoping _ (Or.inl rfl) (x := 3 / 2)
    (by norm_num) (k := 1) (p := 1) (r := 2) (t := 2) (m := 2)
    (hk := by decide) (hr := by decide) (ht := by decide) (hm := by decide) (htp := by decide)
  have hindex (n : ℕ) : 2 * 1 * (n + 1) + 2 = 2 * n + 4 := by omega
  have hprev (n : ℕ) : 2 * n + 4 - 2 = 2 * n + 2 := by omega
  simp only [hindex, Nat.mul_one, hprev] at h
  convert h using 1
  rw [sqrt_discriminant]
  norm_num [generalizedFibonacciPolynomial]

-- With t < 2p and k = 2, the Lucas ratios start below their limit of 2.
example : HasSum (fun n : ℕ =>
    L ((2 * n + 1) * 2 + 1) / L ((2 * n + 1) * 2) -
      L ((2 * n + 3) * 2 + 1) / L ((2 * n + 3) * 2)) (-5 / 34 : ℝ) := by
  have h := hasSum_gibonacciPoly_pow_ratio_telescoping _ (Or.inr rfl) (x := 3 / 2)
    (by norm_num) (k := 2) (p := 1) (r := 1) (t := 1) (m := 1)
    (hk := by decide) (hr := by decide) (ht := by decide) (hm := by decide) (htp := by decide)
  have hindex (n : ℕ) : 2 * 1 * (n + 1) + 1 = 2 * n + 3 := by omega
  have hprev (n : ℕ) : 2 * n + 3 - 2 = 2 * n + 1 := by omega
  simp only [hindex, Nat.mul_one, hprev, pow_one] at h
  convert h using 1
  rw [sqrt_discriminant]
  norm_num [generalizedFibonacciPolynomial, map_ofNat]

end MetaMathlibExt.hasSum_gibonacciPoly_pow_ratio_telescoping
