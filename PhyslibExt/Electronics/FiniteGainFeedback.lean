/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-gain feedback amplifiers

A memoryless finite-gain negative-feedback amplifier with gain
`A > 0` and feedback factor `beta > 0` obeys
`vo = A * (vi - beta * vo)`. This module solves that equation
explicitly and proves the exact gain deficit of the closed-loop gain
`A / (1 + A * beta)` relative to the ideal `1 / beta`: it is
`1 / (beta * (1 + A * beta))`, hence positive. No bandwidth, slew,
stability, loading or transistor-validity claim is made.

Discharges ECE roadmap leaf `ECE.EL.AMPLIFIER.L1` (finite-gain
amplifier model).
-/

@[expose] public section

namespace PhyslibExt.Electronics.FiniteGainFeedback

/-- The loop denominator `1 + A * beta` is strictly positive. -/
theorem one_add_mul_pos {A beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    0 < 1 + A * beta := by
  have h : 0 < A * beta := mul_pos hA hbeta
  linarith

/-- Any output satisfying the amplifier equation has the closed form
`A * vi / (1 + A * beta)`. -/
theorem eq_closedForm_of_eq {A beta vi vo : ℝ} (hA : 0 < A) (hbeta : 0 < beta)
    (h : vo = A * (vi - beta * vo)) :
    vo = A * vi / (1 + A * beta) := by
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  have hne : (1 + A * beta) ≠ 0 := ne_of_gt hpos
  rw [eq_div_iff hne]
  linarith

/-- The closed-form value indeed satisfies the amplifier equation, so
the equation has a solution for every input. -/
theorem closedForm_satisfies {A beta vi : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    A * vi / (1 + A * beta)
      = A * (vi - beta * (A * vi / (1 + A * beta))) := by
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  have hne : (1 + A * beta) ≠ 0 := ne_of_gt hpos
  field_simp
  ring

/-- The closed-loop gain `A / (1 + A * beta)`, as the ratio of the
closed-form output to unit input. -/
theorem closed_loop_gain {A beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    A * 1 / (1 + A * beta) = A / (1 + A * beta) := by
  rw [mul_one]

/-- The exact gain deficit identity:
`1 / beta - A / (1 + A * beta) = 1 / (beta * (1 + A * beta))`. -/
theorem gain_deficit {A beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    1 / beta - A / (1 + A * beta) = 1 / (beta * (1 + A * beta)) := by
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  have hne : (1 + A * beta) ≠ 0 := ne_of_gt hpos
  have hbne : beta ≠ 0 := ne_of_gt hbeta
  field_simp
  ring

/-- The closed-loop gain is positive and below the ideal gain
`1 / beta`; equivalently the deficit is positive. -/
theorem closed_loop_gain_pos_and_lt {A beta : ℝ} (hA : 0 < A)
    (hbeta : 0 < beta) :
    0 < A / (1 + A * beta) ∧ A / (1 + A * beta) < 1 / beta := by
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  refine ⟨div_pos hA hpos, ?_⟩
  have hdef := gain_deficit hA hbeta
  have hpos2 : 0 < 1 / (beta * (1 + A * beta)) := by
    apply one_div_pos.mpr
    exact mul_pos hbeta hpos
  linarith

end PhyslibExt.Electronics.FiniteGainFeedback
