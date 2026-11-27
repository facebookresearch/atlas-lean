/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.AlzerRichardsVanishingStirlingSum

open Finset MetaMathlibExt

-- At r = 0 and the minimum m = 1, both endpoints contribute.
example :
    ∑ k ∈ range 2, (-1 : ℚ) ^ k * ((Nat.choose 1 k : ℚ) / ((0 + k).choose k : ℚ)) *
      (Nat.stirlingSecond (0 + k) k : ℚ) = 0 :=
  sum_choose_div_choose_mul_stirlingSecond_eq_zero (m := 1) (by decide) 0

-- Check the API when m = 1 and r is positive, so the lower Bernoulli bound is tight.
example :
    ∑ k ∈ range 3, (-1 : ℚ) ^ k * ((Nat.choose 2 k : ℚ) / ((1 + k).choose k : ℚ)) *
      (Nat.stirlingSecond (1 + k) k : ℚ) = 0 :=
  sum_choose_div_choose_mul_stirlingSecond_eq_zero (m := 1) (by decide) 1

-- Independently evaluate a case with m = 2 and r = 2, where the weights have denominators > 1.
example :
    ∑ k ∈ range 5, (-1 : ℚ) ^ k * ((Nat.choose 4 k : ℚ) / ((2 + k).choose k : ℚ)) *
      (Nat.stirlingSecond (2 + k) k : ℚ) = 0 := by
  norm_num [sum_range_succ, Nat.choose, Nat.stirlingSecond]
