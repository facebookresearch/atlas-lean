/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Orbital forcing groundwork and elementary planetary mechanics

## i. Overview

For a stipulated inverse-square circular orbit, `v² = G * M / r` and `T = 2πr / v` with `G, M, r, v
  > 0` imply Kepler's third law `T² = 4π²r³ / (GM)`. Elliptic orbits are not covered; the circular
  force balance is a hypothesis.

## ii. Key results

- `EarthScience.kepler_third_law`: `T² = 4π²r³ / (GM)`.
- `EarthScience.kepler_circular_speed`: `v = √(GM / r)`.

## iii. Table of contents

- A. Kepler's third law

## iv. References

- `Real.sqrt_sq`, `Real.pi` in Mathlib.
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Kepler's third law for a stipulated circular orbit: `v ^ 2 = G * M / r`
and `T = 2 * π * r / v` with `G, M, r, v > 0` imply
`T ^ 2 = 4 * π ^ 2 * r ^ 3 / (G * M)`. -/
theorem kepler_third_law {G M r v T : ℝ} (hG : 0 < G) (hM : 0 < M)
    (hr : 0 < r) (hv : 0 < v)
    (hbal : v ^ 2 = G * M / r) (hT : T = 2 * Real.pi * r / v) :
    T ^ 2 = 4 * Real.pi ^ 2 * r ^ 3 / (G * M) := by
  rw [hT, div_pow, hbal]
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hG0 : G ≠ 0 := ne_of_gt hG
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hGM : G * M ≠ 0 := mul_ne_zero hG0 hM0
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Circular-orbit speed: from `v ^ 2 = G * M / r` and `v > 0`,
`v = Real.sqrt (G * M / r)`. -/
theorem kepler_circular_speed {G M r v : ℝ} (hG : 0 < G) (hM : 0 < M)
    (hr : 0 < r) (hv : 0 < v) (hbal : v ^ 2 = G * M / r) :
    v = Real.sqrt (G * M / r) := by
  have h : Real.sqrt (v ^ 2) = v := Real.sqrt_sq hv.le
  rw [hbal] at h
  exact h.symm

end EarthScience
