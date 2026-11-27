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

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
