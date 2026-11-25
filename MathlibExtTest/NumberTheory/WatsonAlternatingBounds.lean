/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import MathlibExt.NumberTheory.WatsonAlternatingBounds

open MetaMathlibExt Real

-- Both inequalities are strict at the first admissible index.
example : 0.252 < 4 * (watsonAlternatingCosecantSum 4 - 8 * log 2 / π) ∧
    4 * (watsonAlternatingCosecantSum 4 - 8 * log 2 / π) < 0.262 := by
  obtain ⟨hl, hu⟩ := watson_alternating_simple_bounds 4 (by decide) (by decide)
  norm_num at hl hu
  constructor <;> linarith only [hl, hu]

-- The preceding even index falls strictly below the claimed lower bound.
example : watsonAlternatingCosecantSum 2 < 4 * log 2 / π + 0.252 / 2 := by
  rw [watsonAlternatingCosecantSum_two]
  have h : 0.874 < 4 * log 2 / π := by
    rw [lt_div_iff₀ pi_pos]
    linarith only [log_two_gt_d9, pi_lt_d4]
  linarith
