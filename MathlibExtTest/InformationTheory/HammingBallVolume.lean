/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.HammingBallVolume

open MathlibExt.InformationTheory.HammingBallVolume

-- Binary, `p = 1/2`, `n = 2`, radius 1: `1 + 2 = 3 ≤ exp (2 · log 2) = 4`.
example : ((∑ i ∈ Finset.range (1 + 1), Nat.choose 2 i * (2 - 1) ^ i : ℕ) : ℝ) ≤
    Real.exp (2 * Real.qaryEntropy 2 (1 / 2)) :=
  sum_choose_mul_pow_le_exp (q := 2) (n := 2) (e := 1) le_rfl (by norm_num) (by norm_num)
    (by norm_num)

-- Boundary `p = 0`: only the radius 0 is allowed and the bound is `1 ≤ exp 0`.
example (n : ℕ) : ((∑ i ∈ Finset.range (0 + 1), n.choose i * (3 - 1) ^ i : ℕ) : ℝ) ≤
    Real.exp (n * Real.qaryEntropy 3 0) :=
  sum_choose_mul_pow_le_exp (q := 3) (e := 0) (by norm_num) le_rfl (by norm_num) (by simp)

-- The central binomial term: `n = 4`, `m = 1`: `C(4, 1) (1/4) (3/4)^3 = 27/64 ≥ 1/5`.
example :
    1 / ((4 : ℝ) + 1) ≤ Nat.choose 4 1 * ((1 : ℝ) / 4) ^ 1 * (1 - (1 : ℝ) / 4) ^ (4 - 1) := by
  exact_mod_cast central_term_ge (n := 4) (m := 1) (by norm_num) (by norm_num)

-- The lower bound applies to every `p ∈ [0, 1]`, for instance the binary `p = 1/2`.
example : ∃ N : ℕ, ∀ n ≥ N, Real.exp (n * Real.qaryEntropy 2 (1 / 2) - 1 / 10 * n) ≤
    ((∑ i ∈ Finset.range (⌊1 / 2 * (n : ℝ)⌋₊ + 1), n.choose i * (2 - 1) ^ i : ℕ) : ℝ) :=
  sum_choose_mul_pow_ge_exp le_rfl (by norm_num) (by norm_num) (by norm_num)
