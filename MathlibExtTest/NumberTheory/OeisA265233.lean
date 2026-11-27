/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OeisA265233
import Mathlib.Tactic.NormNum

/-! # Tests for the Franel number formula for A265233 -/

open MathlibExt.NumberTheory.OeisA265233Wanted

-- The lower bound is sharp: the weighted sum at zero is 1, while six times a₀ is 6.
example : a265233 0 ≠ (1 / 6) * ∑ m ∈ Finset.range (0 + 1),
    (Nat.choose 0 m : ℚ) * 4 ^ (0 - m) * (MetaMathlibExt.binomialPowerSeq 3 0 m : ℚ) := by
  norm_num [a265233, MetaMathlibExt.binomialPowerSeq]

-- Both descriptions give 495 at the first index covered by the recurrence.
example : a265233 4 = 495 := by
  norm_num [a265233]

example : a265233 4 = 495 := by
  rw [a265233_eq_sum_franel (hn := by decide)]
  norm_num [MetaMathlibExt.binomialPowerSeq, Finset.sum_range_succ, Nat.choose]
