/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.MemLpOfLqIntegrableOnFiniteMeasureSets
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open MathlibExt.MeasureTheory.MemLpOfLqIntegrableOnFiniteMeasureSetsWanted
open scoped ENNReal

-- The indicator is above the cutoff on its support and below it on the complement.
private noncomputable def f : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator fun _ => 2

example : MemLp f 2 volume := by
  refine memLp_of_memLp_of_lintegral_rpow_lt_top_of_measure_lt_top
    (p := 1) (q := 2) le_rfl (by norm_num) (by simp) f ?_ ?_
  · exact memLp_indicator_const _ measurableSet_Icc.nullMeasurableSet _
      (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  · intro A _ hA
    calc
      (∫⁻ x in A, (ENNReal.ofReal |f x|) ^ (2 : ℝ≥0∞).toReal ∂volume) ≤
          ∫⁻ _ in A, (4 : ℝ≥0∞) ∂volume := by
        apply lintegral_mono
        intro x
        classical
        by_cases hx : x ∈ Icc (0 : ℝ) 1
        · simp only [f, indicator_of_mem hx]
          norm_num [ENNReal.rpow_two]
        · simp only [f, indicator_of_notMem hx]
          norm_num [ENNReal.rpow_two]
      _ < ∞ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_lt_top (by simp) hA
