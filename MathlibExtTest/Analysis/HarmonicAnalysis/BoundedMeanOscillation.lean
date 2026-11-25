/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillation

/-!
# Tests for the John–Nirenberg inequality

The indicator of `[0,1]` oscillates by exactly `1/2` about its average on `[-1,1]`.
The exceptional set fills that interval below this threshold and is empty at equality.
-/

open MeasureTheory Set
open scoped ENNReal
open MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted

namespace MathlibExtTest.Analysis.HarmonicAnalysis.BoundedMeanOscillation

private noncomputable abbrev step : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator fun _ => 1

private theorem step_integrable : LocallyIntegrable step :=
  (locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Icc

private theorem step_values (x : ℝ) : step x = 0 ∨ step x = 1 := by
  by_cases h : x ∈ Icc (0 : ℝ) 1 <;> simp [step, h]

private theorem step_osc (a b : ℝ) (hab : a < b) :
    (⨍ x in Icc a b, |step x - ⨍ y in Icc a b, step y|) ≤ 1 := by
  let I := Icc a b
  have hI : volume I ≠ 0 := by simp [I, Real.volume_Icc, hab]
  have hfin : volume I ≠ ⊤ := isCompact_Icc.measure_ne_top
  have hi : IntegrableOn step I := step_integrable.integrableOn_isCompact isCompact_Icc
  obtain ⟨x, _, hx⟩ := exists_le_setAverage hI hfin hi
  obtain ⟨y, _, hy⟩ := exists_setAverage_le hI hfin hi
  have hm₀ : 0 ≤ ⨍ z in I, step z :=
    (show 0 ≤ step x by rcases step_values x with h | h <;> simp [h]).trans hx
  have hm₁ : (⨍ z in I, step z) ≤ 1 :=
    hy.trans (by rcases step_values y with h | h <;> simp [h])
  obtain ⟨z, _, hz⟩ := exists_setAverage_le hI hfin
    (hi.sub (integrableOn_const (C := ⨍ z in I, step z) hfin)).abs
  refine hz.trans (abs_le.mpr ?_)
  simp only [Pi.sub_apply]
  rcases step_values z with h | h <;> rw [h] <;> constructor <;> linarith

private theorem step_deviation (x : ℝ) :
    |step x - ⨍ y in Icc (-1 : ℝ) 1, step y| = 1 / 2 := by
  have hmean : (⨍ y in Icc (-1 : ℝ) 1, step y) = 1 / 2 := by
    rw [setAverage_eq, setIntegral_indicator measurableSet_Icc]
    rw [inter_eq_right.mpr (Icc_subset_Icc_left (by norm_num : (-1 : ℝ) ≤ 0))]
    norm_num [Real.volume_real_Icc_of_le, Real.volume_Icc, measureReal_def]
  rw [hmean]
  rcases step_values x with h | h <;> rw [h] <;> norm_num

example : ∃ c : ℝ, 0 < c ∧ (2 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * Real.exp (-(1 / 4) / c)) := by
  obtain ⟨c, hc, h⟩ := exists_volume_abs_sub_average_gt_le
  refine ⟨c, hc, ?_⟩
  have ht := h step step_integrable 1 one_pos step_osc (-1) 1 (by norm_num) (1 / 4) (by norm_num)
  norm_num [step_deviation] at ht
  change volume (Icc (-1 : ℝ) 1) ≤ _ at ht
  rw [Real.volume_Icc] at ht
  norm_num at ht ⊢
  exact ht

example : {x | x ∈ Icc (-1 : ℝ) 1 ∧ 1 / 2 < |step x - ⨍ y in Icc (-1 : ℝ) 1, step y|} = ∅ := by
  simp [step_deviation]

end MathlibExtTest.Analysis.HarmonicAnalysis.BoundedMeanOscillation
