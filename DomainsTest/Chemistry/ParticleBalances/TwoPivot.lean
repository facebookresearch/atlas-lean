/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ParticleBalances.TwoPivot
import Mathlib.Tactic.NormNum

open Domains.Chemistry.ParticleBalances.TwoPivot

-- An interior point with unequal weights gives a strictly positive excess.
example : (2 / 3 : ℝ) * 1 + (1 / 3 : ℝ) * 4 = 2 ∧
    (2 / 3 : ℝ) * 1 ^ 2 + (1 / 3 : ℝ) * 4 ^ 2 - 2 ^ 2 = 2 := by
  have h := two_pivot_moments 1 4 2 (by norm_num) (by norm_num)
  have hm := h.2.1
  have hs := h.2.2.2.1
  change ((4 - 2) / (4 - 1) : ℝ) * 1 + ((2 - 1) / (4 - 1) : ℝ) * 4 = 2 at hm
  change ((4 - 2) / (4 - 1) : ℝ) * 1 ^ 2 + ((2 - 1) / (4 - 1) : ℝ) * 4 ^ 2 - 2 ^ 2 =
    (2 - 1) * (4 - 2) at hs
  simpa only [show (4 : ℝ) - 2 = 2 by norm_num, show (4 : ℝ) - 1 = 3 by norm_num,
    show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using And.intro hm hs

-- An endpoint lies in the nonnegative-weight interval.
example : 0 ≤ ((4 - 4) / (4 - 1) : ℝ) ∧ 0 ≤ ((4 - 1) / (4 - 1) : ℝ) :=
  (two_pivot_moments 1 4 4 (by norm_num) (by norm_num)).2.2.1.mpr ⟨by norm_num, le_rfl⟩

-- To the right of the interval, the first weight is negative.
example : ((4 - 5) / (4 - 1) : ℝ) < 0 :=
  (two_pivot_moments 1 4 5 (by norm_num) (by norm_num)).2.2.2.2.2.2.2 (by norm_num)
