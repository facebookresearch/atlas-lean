/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsEvenBinomialSum
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- At x = 0 the regular formula gives complete cancellation for every admissible m.
example {m : ℕ} (hm : 2 ≤ m) (hme : Even m) :
    ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose (m : ℂ) (m - k) /
      (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m / 2 - 1 / 2) k) = 0 := by
  have h : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simpa using (sum_choose_mul_choose_div_choose_of_even hm hme 0).1
    (div_ne_zero (neg_ne_zero.mpr h) (by norm_num)).symm

-- For m = 2 the exceptional argument gives a nonzero sum even though x + m/2 vanishes.
example :
    ∑ k ∈ range 2, ((2 - k).choose k : ℂ) * Ring.choose (1 : ℂ) (2 - k) /
      (2 ^ (2 * k) * Ring.choose ((k : ℂ) - 1 - 1 / 2) k) = -1 / 2 := by
  have h := (sum_choose_mul_choose_div_choose_of_even (m := 2) le_rfl (by decide) (-1)).2
    (by norm_num)
  norm_num [Ring.choose_one_right] at h ⊢
  exact h
