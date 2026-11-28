/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RogersDilogHoorfarQiSeries
import Mathlib.Tactic.NormNum

open MetaMathlibExt

private noncomputable abbrev L (x : ℝ) : ℝ :=
  (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + Real.log x * Real.log (1 - x) / 2

-- The smallest positive shifts leave one term in each finite sum.
example :
    ∑' n : ℕ, L ((1 / 8) * (1 / 2) ^ n /
        ((1 - (1 / 2) * (1 / 2) ^ (n + 1)) * (1 - (1 / 2) * (1 / 2) ^ (n + 1)))) =
      L (1 / 3) + L (2 / 3) - L (1 / 2) := by
  have h := rogersDilog_hoorfarQi_series (p := 1) (q := 1) (θ := 1 / 2) (β := 1 / 2)
    (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [L, Finset.sum_range_succ] at h ⊢
  exact h

-- With unequal shifts, the first sum has two terms and the second has one.
example :
    ∑' n : ℕ, L ((3 / 16) * (1 / 2) ^ n /
        ((1 - (1 / 2) * (1 / 2) ^ (n + 1)) * (1 - (1 / 2) * (1 / 2) ^ (n + 2)))) =
      L (1 / 3) + L (1 / 7) + L (6 / 7) - L (3 / 4) := by
  have h := rogersDilog_hoorfarQi_series (p := 1) (q := 2) (θ := 1 / 2) (β := 1 / 2)
    (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [L, Finset.sum_range_succ] at h ⊢
  exact h
