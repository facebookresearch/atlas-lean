/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Measure.PositiveMeasureThreeTermProgression
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open MathlibExt.MeasureTheory.PositiveMeasureThreeTermProgressionWanted
open scoped ENNReal

example : ∃ x ∈ Icc (2 : ℝ) 3, ∃ y : ℝ, 0 < y ∧ x + y ∈ Icc (2 : ℝ) 3 ∧
    x - y ∈ Icc (2 : ℝ) 3 := by
  apply exists_add_mem_and_sub_mem_of_volume_pos _ measurableSet_Icc
  rw [Real.volume_Icc, ENNReal.ofReal_pos]
  norm_num

-- The theorem requires neither boundedness nor finite measure of the given set.
example : ∃ x ∈ (Ici (0 : ℝ)), ∃ y : ℝ, 0 < y ∧ x + y ∈ Ici (0 : ℝ) ∧
    x - y ∈ Ici (0 : ℝ) := by
  apply exists_add_mem_and_sub_mem_of_volume_pos _ measurableSet_Ici
  simp [Real.volume_Ici]
