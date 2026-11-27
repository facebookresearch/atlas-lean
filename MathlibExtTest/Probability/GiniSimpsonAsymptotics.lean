/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.GiniSimpsonAsymptotics
import Mathlib.Tactic.NormNum

open Filter MathlibExt.Probability.DiversityStatisticsWanted

-- The last sample size covered by the bounded arithmetic certificate.
example : (197 : ℚ) ≤ giniSimpsonCount 47 := by
  convert giniSimpsonCount_ge 47 using 1
  norm_num

-- An odd sample size in the large case, with a nonintegral lower bound.
example : (431 / 2 : ℚ) ≤ giniSimpsonCount 49 := by
  convert giniSimpsonCount_ge 49 using 1
  norm_num

-- A coefficient strictly below one half gives an eventual quadratic lower bound.
example {c : ℝ} (hc : c < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, c * N ^ 2 < giniSimpsonCount N := by
  filter_upwards [giniSimpsonCount_asymp.eventually_const_lt hc, eventually_gt_atTop 0]
    with N h hN
  exact (lt_div_iff₀ (by positivity)).mp h
