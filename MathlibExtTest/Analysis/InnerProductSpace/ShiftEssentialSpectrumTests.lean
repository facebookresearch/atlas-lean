/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ShiftEssentialSpectrum

import Mathlib.Tactic.NormNum

/-!
# Tests for the essential spectrum of the unilateral shift

* The essential spectrum of the shift on `ℓ²(ℕ, ℂ)` is the unit circle:
  `1`, `-1`, and `I` are in it; `0`, `1/2`, and `2` are not.
* On `ℓ²(ℕ, ℝ)`, `-1` and `1` are in the essential spectrum, `0` is not.
* Fredholmness and index on both sides of the circle: `S - (1/2) • 1`
  is Fredholm of index `-1`; `S - 2 • 1` is Fredholm of index `0`;
  `S - 1 • 1` is not Fredholm.
* The shift itself is Fredholm of index `-1`.
-/

open scoped _root_.lp

namespace MathlibExtTest.Analysis.InnerProductSpace.ShiftEssentialSpectrumTests

open MathlibExt.Analysis.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.ShiftEssentialSpectrum

/-- The essential spectrum of the shift is the unit circle. -/
example : essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℂ)) = Metric.sphere 0 1 :=
  essentialSpectrum_shiftCLM

/-- `1` is in the essential spectrum of the shift over `ℂ`. -/
example : (1 : ℂ) ∈ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℂ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `-1` is in the essential spectrum of the shift over `ℂ`. -/
example : (-1 : ℂ) ∈ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℂ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `I` is in the essential spectrum of the shift over `ℂ`. -/
example : Complex.I ∈ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℂ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `0` is not in the essential spectrum of the shift over `ℂ`. -/
example : (0 : ℂ) ∉ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℂ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `1/2` is not in the essential spectrum of the shift over `ℂ`. -/
example : (1 / 2 : ℂ) ∉ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℂ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `2` is not in the essential spectrum of the shift over `ℂ`. -/
example : (2 : ℂ) ∉ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℂ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `1` is in the essential spectrum of the shift over `ℝ`. -/
example : (1 : ℝ) ∈ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℝ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `-1` is in the essential spectrum of the shift over `ℝ`. -/
example : (-1 : ℝ) ∈ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℝ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- `0` is not in the essential spectrum of the shift over `ℝ`. -/
example : (0 : ℝ) ∉ essentialSpectrum (LpShiftOperator.shiftCLM (𝕜 := ℝ)) := by
  rw [mem_essentialSpectrum_shiftCLM]
  simp

/-- The unilateral shift is a Fredholm operator. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ)).IsFredholm := by
  simpa only [pow_one] using ShiftFredholmIndex.isFredholm_shiftCLM_pow (𝕜 := ℂ) 1

/-- The unilateral shift has Fredholm index `-1`. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ)).index = -1 := ShiftFredholmIndex.index_shiftCLM

/-- `S - (1/2) • 1` is Fredholm. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ) - (1 / 2 : ℂ) • 1).IsFredholm :=
  isFredholm_shift_sub_smul_one_of_norm_lt_one (by
    rw [norm_div, norm_one]
    norm_num [Complex.norm_ofNat])

/-- `S - (1/2) • 1` has Fredholm index `-1`. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ) - (1 / 2 : ℂ) • 1).index = -1 :=
  index_shift_sub_smul_one_of_norm_lt_one (by
    rw [norm_div, norm_one]
    norm_num [Complex.norm_ofNat])

/-- `S - 2 • 1` is Fredholm. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ) - (2 : ℂ) • 1).IsFredholm :=
  isFredholm_shift_sub_smul_one_of_one_lt_norm (by simp)

/-- `S - 2 • 1` has Fredholm index `0`. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ) - (2 : ℂ) • 1).index = 0 :=
  index_shift_sub_smul_one_of_one_lt_norm (by simp)

/-- `S - 1 • 1` is not Fredholm. -/
example : ¬ (LpShiftOperator.shiftCLM (𝕜 := ℂ) - (1 : ℂ) • 1).IsFredholm :=
  not_isFredholm_shift_sub_smul_one_of_norm_eq_one (by simp)

/-- The truncated geometric vectors have squared norm `N + 1`. -/
example : ‖approxVec (1 : ℂ) 3‖ ^ 2 = 4 := by
  rw [norm_sq_approxVec (by simp)]
  norm_num

/-- `(S - 1) applied to the truncated geometric vector has squared norm `2`. -/
example : ‖(LpShiftOperator.shiftCLM (𝕜 := ℂ) - (1 : ℂ) • 1) (approxVec (1 : ℂ) 3)‖ ^ 2 = 2 :=
  norm_sq_sub_smul_one_approxVec (by simp) 3
