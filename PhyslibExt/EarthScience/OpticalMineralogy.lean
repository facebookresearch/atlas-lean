/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Optical mineralogy and anisotropy: phase retardation

## i. Overview

For a lossless two-mode slab with fixed orthogonal polarization modes
and constant refractive indices `n₁, n₂`, thickness `h ≥ 0` and
wavelength `lam > 0`, the phase retardation is
`δ = 2 * π * (n₁ - n₂) * h / lam`, with `h, lam` lengths and `δ` in
radians. No absorption, dispersion, or full indicatrix derivation is
claimed. Degenerate axes are not unique; that is out of scope.

## ii. Key results

- `EarthScience.phaseRetardation_zero_thickness`: `δ = 0` when `h = 0`.
- `EarthScience.phaseRetardation_equal_indices`: `δ = 0` when `n₁ = n₂`.
- `EarthScience.phaseRetardation_example`: `n₁ = 3 / 2, n₂ = 1, h = 1,
  lam = 1` gives `δ = π`.

## iii. Table of contents

- A. Vanishing retardation and a non-vacuous example

## iv. References

- `Real.pi` in Mathlib.

## A. Vanishing retardation and a non-vacuous example
-/

@[expose] public section

namespace EarthScience

/-- Phase retardation of a lossless two-mode slab:
`δ = 2 * π * (n₁ - n₂) * h / lam`, with `h, lam` lengths and `δ` in radians.
`δ = 0` when the thickness `h` is `0`. -/
theorem phaseRetardation_zero_thickness {n₁ n₂ lam : ℝ} (hlam : 0 < lam) :
    2 * Real.pi * (n₁ - n₂) * 0 / lam = 0 := by
  have _ := hlam
  simp

/-- `δ = 0` when the two principal indices coincide (`n₁ = n₂`). -/
theorem phaseRetardation_equal_indices {n h lam : ℝ} (hlam : 0 < lam) :
    2 * Real.pi * (n - n) * h / lam = 0 := by
  have _ := hlam
  simp

/-- Non-vacuous case: `n₁ = 3 / 2, n₂ = 1, h = 1, lam = 1` gives `δ = π`. -/
theorem phaseRetardation_example :
    2 * Real.pi * (3 / 2 - 1) * 1 / 1 = Real.pi := by
  norm_num
  ring

end EarthScience
