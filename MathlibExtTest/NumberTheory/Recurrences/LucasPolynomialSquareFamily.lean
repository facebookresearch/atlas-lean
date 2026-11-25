/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasPolynomialSquareFamily

/-! # Series over Lucas polynomial squares at `x = 3/2` -/

namespace MetaMathlibExt.hasSum_lucasPoly_sq_family

open Polynomial

local notation "L" => fun n : ℕ => aeval (3 / 2 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

private theorem sqrt_discriminant : √((3 / 2 : ℝ) ^ 2 + 4) = 5 / 2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

-- With k = p = r = t = 1 the sign (-1)^(tk) is negative and every term is positive.
example : HasSum (fun n : ℕ => (75 / 8 : ℝ) / (L (2 * n + 2) ^ 2 - 25 / 4)) (5 / 6) := by
  have h := hasSum_lucasPoly_sq_family (x := 3 / 2) (by norm_num)
    (k := 1) (p := 1) (r := 1) (t := 1) (by decide) (by decide) (by decide) (by decide)
  have hindex (n : ℕ) : (2 * 1 * (n + 1) + 1 - 1) * 1 = 2 * n + 2 := by omega
  simp only [hindex] at h
  convert h using 1
  · norm_num [generalizedFibonacciPolynomial]
  · rw [sqrt_discriminant]
    norm_num [generalizedFibonacciPolynomial, map_ofNat]

-- At the boundary t = 2p the sign is positive and every term is negative.
example : HasSum (fun n : ℕ => (-75 / 8 : ℝ) / (L (2 * n + 3) ^ 2 + 25 / 4)) (-5 / 34) := by
  have h := hasSum_lucasPoly_sq_family (x := 3 / 2) (by norm_num)
    (k := 1) (p := 1) (r := 1) (t := 2) (by decide) (by decide) (by decide) (by decide)
  have hindex (n : ℕ) : (2 * 1 * (n + 1) + 2 - 1) * 1 = 2 * n + 3 := by omega
  simp only [hindex] at h
  convert h using 1
  · norm_num [generalizedFibonacciPolynomial]
  · rw [sqrt_discriminant]
    norm_num [generalizedFibonacciPolynomial, map_ofNat]

-- With p = r = 2 and t = 1 < 2p the limit of the ratios is α² = 4.
example : HasSum (fun n : ℕ => (3825 / 64 : ℝ) / (L (4 * n + 3) ^ 2 - 225 / 16)) (5 / 4) := by
  have h := hasSum_lucasPoly_sq_family (x := 3 / 2) (by norm_num)
    (k := 1) (p := 2) (r := 2) (t := 1) (by decide) (by decide) (by decide) (by decide)
  have hindex (n : ℕ) : (2 * 2 * (n + 1) + 1 - 2) * 1 = 4 * n + 3 := by omega
  simp only [hindex] at h
  convert h using 1
  · norm_num [generalizedFibonacciPolynomial]
  · rw [sqrt_discriminant]
    norm_num [generalizedFibonacciPolynomial, map_ofNat]

end MetaMathlibExt.hasSum_lucasPoly_sq_family
