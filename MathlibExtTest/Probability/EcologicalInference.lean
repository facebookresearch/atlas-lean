/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.EcologicalInference
import Mathlib.Tactic.NormNum

/-! # Equal margins do not imply equal joint cell probabilities -/

open MeasureTheory ProbabilityTheory unitInterval

-- The (1, 1) cell has mass 1/2 in the aligned population, but is absent in the crossed one.
example :
    let half : I := ⟨1 / 2, by constructor <;> norm_num⟩
    let cell : Set (ℝ × ℝ) := {(1, 1)}
    (bernoulliMeasure (1, 1) (0, 0) half).real cell = 1 / 2 ∧
      (bernoulliMeasure (1, 0) (0, 1) half).real cell = 0 := by
  intro half cell
  have hs : MeasurableSet cell := measurableSet_singleton _
  constructor
  · rw [bernoulliMeasure_real_apply_of_mem_of_notMem half hs (by simp [cell])
      (by norm_num [cell, Prod.mk.injEq])]
  · exact bernoulliMeasure_real_apply_of_notMem_of_notMem half hs
      (by norm_num [cell, Prod.mk.injEq]) (by norm_num [cell, Prod.mk.injEq])
