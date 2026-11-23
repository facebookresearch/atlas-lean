/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LinftyNormLeSupLpNormUnitInterval
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open MathlibExt.MeasureTheory.LinftyNormLeSupLpNormUnitIntervalWanted
open scoped ENNReal

-- A nonzero constant attains the same bound at every exponent on the unit interval.
example : eLpNorm (fun _ : ℝ => (-2 : ℝ)) ∞ (volume.restrict (Icc (0 : ℝ) 1)) ≤ 2 := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure μ := ⟨by
    dsimp [μ]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    norm_num⟩
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 1 := measure_univ
    simp [hz] at hu
  have h := eLpNorm_top_le_of_forall_one_le_eLpNorm_le (fun _ _ => (-2 : ℝ)) 2
    (fun _ => aestronglyMeasurable_const) (by
      intro n p hp
      change eLpNorm (fun _ : ℝ => (-2 : ℝ)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal 2
      have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hp)).ne'
      rw [eLpNorm_const _ hp0 hμ, measure_univ, ENNReal.one_rpow, mul_one, ← ofReal_norm]
      norm_num) 0
  simpa using h

-- A negative real bound is interpreted as zero, not as a negative norm.
example : eLpNorm (0 : ℝ → ℝ) ∞ (volume.restrict (Icc (0 : ℝ) 1)) ≤ ENNReal.ofReal (-1) :=
  eLpNorm_top_le_of_forall_one_le_eLpNorm_le (fun _ => 0) (-1)
    (fun _ => aestronglyMeasurable_zero) (by simp) 0
