/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.PowerPorts

/-!
# Particle power-port checks

Concrete consumer of `PhyslibExt.Mechanics.PowerPorts`: mass `2`, start `0` with velocity `1`
and constant force `4` over the elapsed time `1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Constant-force fixture

## iv. References

None.

## A. Constant-force fixture

-/

open PhyslibExt.Mechanics.PowerPorts

/-- Mass `2`, start `0` with velocity `1`, force `4 ≠ 0`, elapsed time `1 > 0`: final velocity
`3`, final position `2`, work `8` (both as the integrated power and as the change of kinetic
energy), and impulse `4`. -/
example :
    constForceVelocity (E := ℝ) 2 1 4 1 = 3 ∧ constForcePosition (E := ℝ) 2 0 1 4 1 = 2 ∧
      ∫ t in (0 : ℝ)..1, inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 t) = 8 ∧
      2 * ‖constForceVelocity (E := ℝ) 2 1 4 1‖ ^ 2 / 2 -
          2 * ‖constForceVelocity (E := ℝ) 2 1 4 0‖ ^ 2 / 2 = 8 ∧
      (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 - (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0
        = 4 := by
  have hm : (0 : ℝ) < 2 := by norm_num
  have hv1 : constForceVelocity (E := ℝ) 2 1 4 1 = 3 := by
    simp [constForceVelocity, smul_eq_mul]
    norm_num
  have hx1 : constForcePosition (E := ℝ) 2 0 1 4 1 = 2 := by
    simp [constForcePosition, smul_eq_mul]
    norm_num
  have hv0 : constForceVelocity (E := ℝ) 2 1 4 0 = 1 := by
    simp [constForceVelocity, smul_eq_mul]
  have hK : 2 * ‖constForceVelocity (E := ℝ) 2 1 4 1‖ ^ 2 / 2 -
      2 * ‖constForceVelocity (E := ℝ) 2 1 4 0‖ ^ 2 / 2 = 8 := by
    rw [hv1, hv0]
    norm_num [Real.norm_eq_abs]
  have hwork := (constForce_work (m := 2) hm (0 : ℝ) (1 : ℝ) (4 : ℝ) (0 : ℝ) (1 : ℝ)).1
  have hwork8 : ∫ t in (0 : ℝ)..1, inner ℝ (4 : ℝ) (constForceVelocity (E := ℝ) 2 1 4 t) = 8 :=
    hwork.trans hK
  have himp : (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 1 -
      (2 : ℝ) • constForceVelocity (E := ℝ) 2 1 4 0 = 4 := by
    rw [hv1, hv0, smul_eq_mul, smul_eq_mul]
    norm_num
  exact ⟨hv1, hx1, hwork8, hK, himp⟩
