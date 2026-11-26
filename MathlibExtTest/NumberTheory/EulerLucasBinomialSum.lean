/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EulerLucasBinomialSum

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open Finset MetaMathlibExt
open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry

private theorem secant_two : eulerSecNumber 2 = -1 := by
  have h := chapter5EulerEven_step 1 (by decide)
  norm_num [Fin.sum_univ_one, chapter5EulerEven_zero] at h
  norm_num [eulerSecNumber, h]

-- Evaluate the first three sums directly, without invoking the general identity.
example :
    (∑ k ∈ range (0 + 1), (Nat.choose 0 k : ℝ) * (Real.sqrt 5 / 2) ^ k *
      (eulerSecNumber k : ℝ) * (lucasNumber (0 - k) : ℝ)) = 2 := by
  norm_num [sum_range_succ, eulerSecNumber, chapter5EulerEven_zero, lucasNumber]

example :
    (∑ k ∈ range (1 + 1), (Nat.choose 1 k : ℝ) * (Real.sqrt 5 / 2) ^ k *
      (eulerSecNumber k : ℝ) * (lucasNumber (1 - k) : ℝ)) = 1 := by
  norm_num [sum_range_succ, eulerSecNumber, chapter5EulerEven_zero, lucasNumber]

example :
    (∑ k ∈ range (2 + 1), (Nat.choose 2 k : ℝ) * (Real.sqrt 5 / 2) ^ k *
      (eulerSecNumber k : ℝ) * (lucasNumber (2 - k) : ℝ)) = 1 / 2 := by
  have he₁ : eulerSecNumber 1 = 0 := rfl
  have he₀ : eulerSecNumber 0 = 1 := by norm_num [eulerSecNumber, chapter5EulerEven_zero]
  norm_num [sum_range_succ, he₀, he₁, secant_two, lucasNumber, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

-- The general expansion at m = 1 and a nonzero x.
example : ((3 : ℝ) + 1 / 2) ^ 1 =
    (1 / 2) * ∑ n ∈ range (1 + 1), ∑ k ∈ range (n + 1),
      (Real.sqrt 5 / 2) ^ k * (n.choose k : ℝ) * ((1 : ℕ).choose n : ℝ) * (3 : ℝ) ^ (1 - n) *
        (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) :=
  add_half_pow_eq_sum 1 3

-- The alternating sum vanishes already at the first allowed degree.
example : (∑ n ∈ range (1 + 1), ∑ k ∈ range (n + 1),
    (-1 : ℝ) ^ n * (Real.sqrt 5) ^ k / 2 ^ (k + 1 - n) * (n.choose k : ℝ) *
      ((1 : ℕ).choose n : ℝ) * (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ)) = 0 :=
  sum_neg_one_pow_eulerSec_lucas 1 (by decide)

-- The unsigned sum includes degree zero.
example : (∑ n ∈ range (0 + 1), ∑ k ∈ range (n + 1),
    (Real.sqrt 5) ^ k / 2 ^ (k + 0 - n) * (n.choose k : ℝ) * ((0 : ℕ).choose n : ℝ) *
      (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ)) = 2 :=
  sum_eulerSec_lucas 0

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
