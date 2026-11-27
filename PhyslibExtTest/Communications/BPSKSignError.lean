/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.BPSKSignError
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Communications.BPSKSignError ProbabilityTheory

namespace PhyslibExtTest.Communications.BPSKSignError

/-- The CDF/Q identity at `x = 1`. -/
example : cdf (gaussianReal 0 1) (-1) = gaussianQ 1 :=
  cdf_neg_eq_gaussianQ 1

/-- The threshold formula at zero threshold and prior `1/2`. -/
example : thresholdErrorFormula (1 / 2) 2 1 0
    = cdf (gaussianReal 0 1) (-2 / 1) :=
  thresholdErrorFormula_half_zero 2 1 (by norm_num)

/-- The energy form at `a = 2`, `σ = 1`, `N0 = 2`:
`a / σ = √(2 * Eb / N0) = 2`. -/
example : (2 : ℝ) / 1 = Real.sqrt (2 * bitEnergy 2 / 2) := by
  have h := div_eq_sqrt_two_bitEnergy_div 2 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

/-- Detector behavior: at the tie `y = τ` the detector returns
`+1`; strictly below threshold it returns `-1`. -/
example : thresholdDetector 0 0 = 1 := by simp [thresholdDetector]

example : thresholdDetector 0 (-1) = -1 := by simp [thresholdDetector]

example : signDetector 0 = 1 := by simp [signDetector, thresholdDetector]

/-- Error-event membership on a two-point sample space: with
label `+1` and a received sample below threshold, the point is in
the error event; with label `-1` it is not. -/
example : (0 : Fin 2) ∈ signErrorEvent (Fin 2) 1 ![1, -1] ![-3, 0] := by
  simp [signErrorEvent, receivedSample, signDetector, thresholdDetector]

example : (1 : Fin 2) ∉ signErrorEvent (Fin 2) 1 ![1, -1] ![-3, 0] := by
  simp [signErrorEvent, receivedSample, signDetector, thresholdDetector]

/-- Unequal priors: for prior `1/4`, amplitude `1` and `σ = 1`,
some nonzero threshold strictly beats the zero threshold. -/
example : ∃ τ : ℝ, thresholdErrorFormula (1 / 4) 1 1 τ
    < thresholdErrorFormula (1 / 4) 1 1 0 :=
  exists_threshold_lt_zero_threshold_of_prior_ne_half (1 / 4) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.Communications.BPSKSignError
