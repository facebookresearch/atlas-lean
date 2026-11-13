/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.DampedOscillator

/-!
# Equilibrium tidal forcing and resonant response

Concrete consumers of `PhyslibExt.EarthScience.DampedOscillator`.

## i. Overview

Numeric case `F = 3`, `γ = 0.5`, `ω₀ = 4`, `ω = 3` (`D = 58`) and the
zero-forcing boundary.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.DampedOscillator`
-/

/-- Numeric coefficients: `F = 3`, `γ = 0.5`, `ω₀ = 4`, `ω = 3`, `D = 58`. -/
example : ((4 : ℝ) ^ 2 - 3 ^ 2) *
      (3 * ((4 : ℝ) ^ 2 - 3 ^ 2) / (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) +
    2 * 0.5 * 3 * (3 * (2 * 0.5 * 3) /
      (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) = 3 ∧
    ((4 : ℝ) ^ 2 - 3 ^ 2) *
      (3 * (2 * 0.5 * 3) / (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) -
    2 * 0.5 * 3 * (3 * ((4 : ℝ) ^ 2 - 3 ^ 2) /
      (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) = 0 :=
  EarthScience.damped_oscillator_coefficients (F := 3) (γ := 0.5) (ω₀ := 4) (ω := 3)
    (by norm_num)

/-- Numeric amplitude: `3 / √58`. -/
example : Real.sqrt ((3 * ((4 : ℝ) ^ 2 - 3 ^ 2) /
      (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) ^ 2 +
    (3 * (2 * 0.5 * 3) /
      (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) ^ 2) =
    |3| / Real.sqrt (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2) :=
  EarthScience.damped_oscillator_amplitude (F := 3) (γ := 0.5) (ω₀ := 4) (ω := 3)
    (by norm_num)

/-- Zero forcing: `F = 0` gives amplitude `0`. -/
example : Real.sqrt (((0 : ℝ) * ((4 : ℝ) ^ 2 - 3 ^ 2) /
      (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) ^ 2 +
    ((0 : ℝ) * (2 * 0.5 * 3) /
      (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2)) ^ 2) =
    |(0 : ℝ)| / Real.sqrt (((4 : ℝ) ^ 2 - 3 ^ 2) ^ 2 + (2 * 0.5 * 3) ^ 2) :=
  EarthScience.damped_oscillator_amplitude (F := 0) (γ := 0.5) (ω₀ := 4) (ω := 3)
    (by norm_num)
