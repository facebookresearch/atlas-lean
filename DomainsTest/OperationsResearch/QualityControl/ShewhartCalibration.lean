/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.OperationsResearch.QualityControl.ShewhartCalibration
import Mathlib.Tactic.NormNum

/-! # Regression tests for the Shewhart calibration margins -/

open OperationsResearch.QualityControl

-- A reading strictly beyond the outer margin certifies a signal.
example (x : ℝ) (hx : |5 - x| ≤ 1) : 3 < |x| := by
  have h := shewhart_signal_of_calibrated_reading 0 5
    (h := 3) (σ := 1) (ε := 1) (by norm_num) (by norm_num) (by norm_num)
  have hs := (h.1 x hx).1 (by norm_num)
  simpa using hs

-- The inner margin is inclusive, including on the lower side of the center line.
example (x : ℝ) (hx : |(-2) - x| ≤ 1) : |x| ≤ 3 := by
  have h := shewhart_signal_of_calibrated_reading 0 (-2)
    (h := 3) (σ := 1) (ε := 1) (by norm_num) (by norm_num) (by norm_num)
  have hs := (h.1 x hx).2 (by norm_num)
  simpa using hs

-- At the outer margin itself both conclusions are possible for the same reading.
example : (∃ x : ℝ, |4 - x| ≤ 1 ∧ 3 < |x|) ∧ (∃ x : ℝ, |4 - x| ≤ 1 ∧ |x| ≤ 3) := by
  have h := shewhart_signal_of_calibrated_reading 0 4
    (h := 3) (σ := 1) (ε := 1) (by norm_num) (by norm_num) (by norm_num)
  have hs := h.2 (by norm_num) (by norm_num)
  simpa using hs

-- When the error bound exceeds the control radius, even a centered reading is ambiguous.
example : (∃ x : ℝ, |-x| ≤ 4 ∧ 3 < |x|) ∧ (∃ x : ℝ, |-x| ≤ 4 ∧ |x| ≤ 3) := by
  have h := shewhart_signal_of_calibrated_reading 2 2
    (h := 3) (σ := 1) (ε := 4) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨⟨x, hx, hs⟩, ⟨y, hy, hn⟩⟩ := h.2 (by norm_num) (by norm_num)
  refine ⟨⟨x - 2, ?_, by simpa using hs⟩, ⟨y - 2, ?_, by simpa using hn⟩⟩
  · simpa only [neg_sub] using hx
  · simpa only [neg_sub] using hy
