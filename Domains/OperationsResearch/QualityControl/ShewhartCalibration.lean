/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Group.Abs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Shewhart control limits with bounded reading error -/

@[expose] public section

namespace OperationsResearch.QualityControl

/-- **Shewhart signal from a calibrated reading.** Let `μ` be the center line, `h > 0`
the control multiplier, `σ > 0` the standard deviation, and `ε ≥ 0` the calibration
error bound. A true value signals when its distance from `μ` exceeds `h * σ`. A reading
within `ε` of the true value certifies a signal if its distance from `μ` exceeds
`h * σ + ε`, and certifies no signal if that distance is at most `h * σ - ε`. In the
remaining band both a signal and a nonsignal are consistent with the reading and the same
error bound. The control-limit convention is from the NIST/SEMATECH *e-Handbook of
Statistical Methods*, §6.3.2. -/
theorem shewhart_signal_of_calibrated_reading (μ reading : ℝ) {h σ ε : ℝ}
    (hh : 0 < h) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    (∀ x : ℝ, |reading - x| ≤ ε →
      (h * σ + ε < |reading - μ| → h * σ < |x - μ|) ∧
      (|reading - μ| ≤ h * σ - ε → |x - μ| ≤ h * σ)) ∧
    (h * σ - ε < |reading - μ| → |reading - μ| ≤ h * σ + ε →
      (∃ x : ℝ, |reading - x| ≤ ε ∧ h * σ < |x - μ|) ∧
      (∃ x : ℝ, |reading - x| ≤ ε ∧ |x - μ| ≤ h * σ)) := by
  have hr : 0 ≤ h * σ := mul_nonneg hh.le hσ.le
  constructor
  · intro x hcal
    have hcal' : |x - reading| ≤ ε := by rwa [abs_sub_comm]
    constructor
    · intro hout
      have htri := abs_sub_le reading x μ
      linarith
    · intro hin
      have htri := abs_sub_le x reading μ
      linarith
  · intro hlo hhi
    by_cases hside : μ ≤ reading
    · have hd : |reading - μ| = reading - μ := abs_of_nonneg (sub_nonneg.mpr hside)
      rw [hd] at hlo hhi
      constructor
      · refine ⟨reading + ε, ?_, ?_⟩
        · rw [show reading - (reading + ε) = -ε by ring, abs_neg, abs_of_nonneg hε]
        · rw [abs_of_nonneg (by linarith : 0 ≤ reading + ε - μ)]
          linarith
      · by_cases hin : reading - μ ≤ h * σ
        · exact ⟨reading, by simpa using hε, hd.trans_le hin⟩
        · refine ⟨μ + h * σ, ?_, ?_⟩
          · rw [abs_of_nonneg (by linarith : 0 ≤ reading - (μ + h * σ))]
            linarith
          · rw [show μ + h * σ - μ = h * σ by ring, abs_of_nonneg hr]
    · have hd : |reading - μ| = -(reading - μ) := abs_of_nonpos (by linarith)
      rw [hd] at hlo hhi
      constructor
      · refine ⟨reading - ε, ?_, ?_⟩
        · rw [show reading - (reading - ε) = ε by ring, abs_of_nonneg hε]
        · rw [abs_of_nonpos (by linarith : reading - ε - μ ≤ 0)]
          linarith
      · by_cases hin : -(reading - μ) ≤ h * σ
        · exact ⟨reading, by simpa using hε, hd.trans_le hin⟩
        · refine ⟨μ - h * σ, ?_, ?_⟩
          · rw [abs_of_nonpos (by linarith : reading - (μ - h * σ) ≤ 0)]
            linarith
          · rw [show μ - h * σ - μ = -(h * σ) by ring, abs_neg, abs_of_nonneg hr]

end OperationsResearch.QualityControl
