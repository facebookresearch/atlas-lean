/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.SynchronousPowerAngle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

open PhyslibExt.Circuits.SynchronousPowerAngle

namespace PhyslibExtTest.Circuits.SynchronousPowerAngle

/-- At zero load angle, with `E = 3`, `V = 2`, and `Xs = 2`, the real
power is `0` and the reactive power is `3`. -/
example : realPower 3 2 2 0 = 0 ∧ reactivePower 3 2 2 0 = 3 := by
  have h := power_at_zero_angle 3 2 2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  norm_num

/-- At a positive load angle below `pi`, with `E = 3`, `V = 2`, and
`Xs = 2`, the real power is positive. -/
example : 0 < realPower 3 2 2 (Real.pi / 2) := by
  apply realPower_pos_of_angle_pos 3 2 2 (Real.pi / 2) (by norm_num) (by norm_num)
    (by norm_num)
  · have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  · have hpi : 0 < Real.pi := Real.pi_pos
    have h : Real.pi / 2 < Real.pi := by linarith
    exact h

/-- Negating the current negates the total complex power, checked at
terminal voltage `2` and unit current. -/
example : totalComplexPower 2 (-(1 : ℂ)) = -totalComplexPower 2 (1 : ℂ) :=
  totalComplexPower_neg_current 2 (1 : ℂ)

end PhyslibExtTest.Circuits.SynchronousPowerAngle
