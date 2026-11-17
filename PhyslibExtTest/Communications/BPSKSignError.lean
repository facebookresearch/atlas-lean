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

end PhyslibExtTest.Communications.BPSKSignError
