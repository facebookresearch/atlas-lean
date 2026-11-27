/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ScherkRisingFactorials

namespace MathlibExtTest.ScherkRisingFactorials

open MetaMathlibExt Polynomial

-- At order zero the empty product leaves every coefficient unchanged.
example (s : ℝ) (S : ℕ → ℕ → ℝ) (hS : IsHsuShiueFamily S (-s) 1 0)
    (a : ℕ → ℝ) (N : ℕ) (x : ℝ) (hx : 0 < x) :
    ∑ k ∈ Finset.range (N + 1), a k * x ^ k =
      (∑ k ∈ Finset.range (N + 1), C (a k) * X ^ k).eval x := by
  simpa [hS.2.1, generalizedFallingFactorial] using
    sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative s S hS a N 0 x hx

-- At step -3/2 and order two, the second derivative of 1 + X vanishes.
-- The linear coefficient contributes (1 - 3/2) times 2 raised to the power -2.
example (S : ℕ → ℕ → ℝ) (hS : IsHsuShiueFamily S (3 / 2) 1 0) :
    ∑ i ∈ Finset.range 3, S 2 i * (2 : ℝ) ^ ((-3 : ℝ) + i) *
      (derivative^[i] (1 + X : ℝ[X])).eval 2 = -1 / 8 := by
  have h := sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative (-3 / 2) S
    (by simpa only [neg_div, neg_neg] using hS) (fun _ => 1) 1 2 2 (by norm_num)
  norm_num [Finset.sum_range_succ, Finset.prod_range_succ] at h ⊢
  exact h.symm

end MathlibExtTest.ScherkRisingFactorials
