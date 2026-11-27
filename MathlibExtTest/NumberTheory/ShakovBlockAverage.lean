/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ShakovBlockAverage
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open MathlibExt.NumberTheory.ShakovTwoRegularWanted

-- The zeroth block consists of index one and has average zero.
example : (∑ t ∈ Finset.Ico 1 2, (shakovSeq t : ℝ)) = 0 := by
  simpa using block_average 0

-- The block starting at eight has average 23/4.
example : (1 / (8 : ℝ)) * (∑ t ∈ Finset.Ico 8 16, (shakovSeq t : ℝ)) = 23 / 4 := by
  have h := block_average 3
  norm_num at h
  rw [h]
  have hs : Real.sqrt 17 ≠ 0 := by positivity
  field_simp
  linear_combination 8 * Real.sqrt 17 * Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
