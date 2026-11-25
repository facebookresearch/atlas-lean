/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.RamseyThreeUpper
import Mathlib.Tactic.NormNum

open Filter SimpleGraph MathlibExt.Combinatorics.RamseyThreeTWanted

/-- Specialize the error to one half and clear the eventually positive logarithm. -/
example : ∀ᶠ t : ℕ in atTop,
    (graphRamsey 3 t : ℝ) * Real.log t ≤ (3 / 2 : ℝ) * t ^ 2 := by
  filter_upwards [graphRamsey_three_upper (ε := 1 / 2) (hε := by norm_num),
    eventually_gt_atTop 1] with t h ht
  have hlog := Real.log_pos (by exact_mod_cast ht : (1 : ℝ) < t)
  rw [← mul_div_assoc, le_div_iff₀ hlog] at h
  norm_num at h ⊢
  exact h
