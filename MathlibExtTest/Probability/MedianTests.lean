/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Median
import Mathlib.Tactic.NormNum

/-!
# Tests for medians

Medians need not be unique: for the fair coin `(δ₀ + δ₁) / 2` on `ℝ`, both `0` and `1` are
medians, and each minimizes the expected absolute deviation.
-/

namespace MathlibExtTest.Median

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The fair coin on `{0, 1} ⊆ ℝ`. -/
noncomputable def coin : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

instance : IsProbabilityMeasure coin := ⟨by
  simp [coin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

theorem isMedian_coin_zero : IsMedian coin 0 := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [coin, measureReal_def, ENNReal.toReal_inv, ENNReal.inv_two_add_inv_two]

theorem isMedian_coin_one : IsMedian coin 1 := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [coin, measureReal_def, ENNReal.toReal_inv, ENNReal.inv_two_add_inv_two]

example (y : ℝ) : ∫ θ, |θ - 0| ∂coin ≤ ∫ θ, |θ - y| ∂coin :=
  integral_abs_sub_le_of_isMedian coin isMedian_coin_zero y

example (y : ℝ) : ∫ θ, |θ - 1| ∂coin ≤ ∫ θ, |θ - y| ∂coin :=
  integral_abs_sub_le_of_isMedian coin isMedian_coin_one y

end MathlibExtTest.Median
