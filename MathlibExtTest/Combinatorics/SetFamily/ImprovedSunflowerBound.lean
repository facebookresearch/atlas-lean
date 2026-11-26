/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.ImprovedSunflowerBound

/-! # Tests for the absolute sunflower bound constant -/

open MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemma Real

-- At the smallest admissible parameters, even equality at the ALWZ threshold clears the
-- strict uniform threshold. In particular the small, positive iterated logarithm is not lost.
example {n : ℕ} (h : lowerBound 3 C 2 ≤ n) : (1024 * 3 * logb 2 6) ^ 2 < n := by
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 10 = 1024 by norm_num,
    show (2 : ℝ) * 3 = 6 by norm_num] using
    (uniformThreshold_lt_lowerBound (r := 3) (w := 2) (by decide) (by decide)).trans_le h

-- The width restriction cannot simply be dropped: the formula degenerates at width one.
example : lowerBound 3 C 1 = 0 := by simp [lowerBound]
