/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Thiem well flow in a steady confined aquifer

In steady confined radial flow with constant transmissivity `T`, pumping
rate `Q`, no distributed recharge and finite radii, the head profile is
`h(r) = C + Q * log r / (2 * π * T)`, so the head rise from `r1` to `r2`
is `h(r2) - h(r1) = Q * log (r2 / r1) / (2 * π * T)`.

## i. Overview

`C` is an additive constant (the head at unit radius). For pumping
`Q ≥ 0` and `T > 0`, head increases outward for `r1 < r2`: the well
draws the head down toward the well. Zero pumping and equal radii both
give zero head difference. `T` has units length²/time and `Q`
volume/time; no zero-radius well or unconfined reuse is claimed. The
module is self-contained from Mathlib primitives.

## ii. Key results

- `EarthScience.thiem_head_difference`: Thiem head-difference formula.
- `EarthScience.thiem_head_difference_nonneg`: head increases outward under pumping.
- `EarthScience.thiem_head_difference_zero_pumping`: zero pumping gives zero difference.
- `EarthScience.thiem_head_difference_equal_radii`: equal radii give zero difference.

## iii. Table of contents

- A. Thiem head difference

## iv. References

- R. A. Freeze and J. A. Cherry, *Groundwater*, Prentice-Hall (1979),
  Chapter 5 (Groundwater Flow to Wells), for the Thiem equilibrium
  equation for steady radial flow to a well in a confined aquifer.
- `Real.log_div`, `Real.log_nonneg`, `Real.pi_pos` in Mathlib.

## A. Thiem head difference
-/

@[expose] public section

namespace EarthScience

/-- Thiem head difference: for the steady confined radial-flow profile
`h(r) = C + Q * log r / (2 * π * T)`, the head rise from `r1` to `r2`
is `Q * log (r2 / r1) / (2 * π * T)`. -/
theorem thiem_head_difference {Q T C r1 r2 : ℝ} (hT : T ≠ 0)
    (hr1 : 0 < r1) (hr2 : 0 < r2) :
    (C + Q * Real.log r2 / (2 * Real.pi * T)) -
        (C + Q * Real.log r1 / (2 * Real.pi * T)) =
      Q * Real.log (r2 / r1) / (2 * Real.pi * T) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h2T : (2 * Real.pi * T) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hT
  rw [Real.log_div hr2.ne' hr1.ne']
  field_simp
  ring

/-- Thiem head difference: sign of drawdown. For pumping `Q ≥ 0`,
`T > 0` and `r1 < r2`, head increases outward: `h(r2) - h(r1) ≥ 0`. -/
theorem thiem_head_difference_nonneg {Q T C r1 r2 : ℝ} (hQ : 0 ≤ Q) (hT : 0 < T)
    (hr1 : 0 < r1) (hr2 : r1 < r2) :
    0 ≤ (C + Q * Real.log r2 / (2 * Real.pi * T)) -
        (C + Q * Real.log r1 / (2 * Real.pi * T)) := by
  have h := thiem_head_difference (Q := Q) (C := C) (ne_of_gt hT) hr1
    (lt_trans hr1 hr2)
  rw [h]
  have hlog : 0 ≤ Real.log (r2 / r1) :=
    Real.log_nonneg ((one_le_div hr1).mpr (le_of_lt hr2))
  have hden : (0 : ℝ) ≤ 2 * Real.pi * T := by positivity
  exact div_nonneg (mul_nonneg hQ hlog) hden

set_option linter.unusedVariables false in
/-- Thiem head difference: zero pumping gives zero head difference. -/
theorem thiem_head_difference_zero_pumping {T C r1 r2 : ℝ} (hT : T ≠ 0)
    (hr1 : 0 < r1) (hr2 : 0 < r2) :
    (C + 0 * Real.log r2 / (2 * Real.pi * T)) -
        (C + 0 * Real.log r1 / (2 * Real.pi * T)) = 0 := by
  simp

set_option linter.unusedVariables false in
/-- Thiem head difference: equal radii give zero head difference. -/
theorem thiem_head_difference_equal_radii {Q T C r : ℝ} (hT : T ≠ 0)
    (hr : 0 < r) :
    (C + Q * Real.log r / (2 * Real.pi * T)) -
        (C + Q * Real.log r / (2 * Real.pi * T)) = 0 := by
  exact sub_self _

end EarthScience
