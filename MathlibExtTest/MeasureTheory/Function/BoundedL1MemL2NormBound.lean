/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.BoundedL1MemL2NormBound
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set
open MathlibExt.Analysis.FunctionalAnalysis.BoundedL1MemL2NormBoundWanted

-- A nonzero function with bounded support on a space of infinite Lebesgue measure.
example :
    let f := (Icc (0 : Fin 1 → ℝ) 1).indicator (fun _ => (2 : ℝ))
    MemLp f 2 ∧ (eLpNorm f 2).toReal ≤ Real.sqrt 2 * Real.sqrt (eLpNorm f 1).toReal := by
  dsimp only
  apply memLp_two_and_eLpNorm_two_le_of_bounded_of_memLp_one 1 _ 2 (by norm_num)
  · intro x
    by_cases hx : x ∈ Icc (0 : Fin 1 → ℝ) 1 <;> simp [hx]
  · refine memLp_indicator_const 1 measurableSet_Icc.nullMeasurableSet 2 (Or.inr ?_)
    rw [Real.volume_Icc_pi]
    simp
