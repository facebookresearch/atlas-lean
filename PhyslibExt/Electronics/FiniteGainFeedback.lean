/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-gain feedback amplifier

## i. Overview

A memoryless finite-gain negative-feedback amplifier: gain
`A > 0`, feedback factor `beta > 0`, and the amplifier equation
`vo = A * (vi - beta * vo)` relating input `vi` and output `vo`.
Every solution of the equation is the closed-loop gain
`closedLoopGain A beta = A / (1 + A * beta)` times the input, and
the exact gain deficit below the ideal gain `1 / beta` is
`1 / (beta * (1 + A * beta))`.

## ii. Key results

- `eq_closedForm_of_eq`: any output satisfying the amplifier
  equation has the closed form `A * vi / (1 + A * beta)`.
- `closedForm_satisfies`: the closed form satisfies the equation.
- `output_eq_closedLoopGain_mul`: any such output is
  `closedLoopGain A beta * vi`.
- `gain_deficit`: the exact deficit identity through
  `closedLoopGain`.
- `closedLoopGain_pos_and_lt`: the closed-loop gain is positive
  and below the ideal gain `1 / beta`.

## iii. Table of contents

- A. The finite-gain feedback law

## iv. References

- A. S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: the finite-gain feedback
  amplifier equation, its closed-loop gain `A / (1 + A * beta)` and
  the comparison with the ideal gain `1 / beta`.

## A. The finite-gain feedback law
-/

@[expose] public section

namespace PhyslibExt.Electronics.FiniteGainFeedback

/-- The loop denominator `1 + A * beta` is strictly positive. -/
lemma one_add_mul_pos {A beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    0 < 1 + A * beta := by
  have h : 0 < A * beta := mul_pos hA hbeta
  linarith

/-- Any output satisfying the amplifier equation has the closed form
`A * vi / (1 + A * beta)`. -/
lemma eq_closedForm_of_eq {A beta vi vo : ℝ} (hA : 0 < A) (hbeta : 0 < beta)
    (h : vo = A * (vi - beta * vo)) :
    vo = A * vi / (1 + A * beta) := by
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  have hne : (1 + A * beta) ≠ 0 := ne_of_gt hpos
  rw [eq_div_iff hne]
  linarith

/-- The closed-form value indeed satisfies the amplifier equation, so
the equation has a solution for every input. -/
lemma closedForm_satisfies {A beta vi : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    A * vi / (1 + A * beta)
      = A * (vi - beta * (A * vi / (1 + A * beta))) := by
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  have hne : (1 + A * beta) ≠ 0 := ne_of_gt hpos
  field_simp
  ring

/-- The closed-loop gain of the amplifier: the factor multiplying the
input in the closed-form output. -/
noncomputable def closedLoopGain (A beta : ℝ) : ℝ :=
  A / (1 + A * beta)

/-- Any output satisfying the amplifier equation is the closed-loop
gain times the input. This is the amplifier contract for
`closedLoopGain`; it consumes the equation rather than restating
arithmetic. -/
lemma output_eq_closedLoopGain_mul {A beta vi vo : ℝ} (hA : 0 < A)
    (hbeta : 0 < beta) (h : vo = A * (vi - beta * vo)) :
    vo = closedLoopGain A beta * vi := by
  have hcf := eq_closedForm_of_eq hA hbeta h
  unfold closedLoopGain
  rw [hcf]
  ring

/-- The exact gain deficit identity:
`1 / beta - closedLoopGain A beta = 1 / (beta * (1 + A * beta))`. -/
lemma gain_deficit {A beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    1 / beta - closedLoopGain A beta = 1 / (beta * (1 + A * beta)) := by
  unfold closedLoopGain
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  have hne : (1 + A * beta) ≠ 0 := ne_of_gt hpos
  have hbne : beta ≠ 0 := ne_of_gt hbeta
  field_simp
  ring

/-- The closed-loop gain is positive and below the ideal gain
`1 / beta`; equivalently the deficit is positive. -/
lemma closedLoopGain_pos_and_lt {A beta : ℝ} (hA : 0 < A)
    (hbeta : 0 < beta) :
    0 < closedLoopGain A beta ∧ closedLoopGain A beta < 1 / beta := by
  have hpos : 0 < 1 + A * beta := one_add_mul_pos hA hbeta
  have hdef := gain_deficit hA hbeta
  have hpos2 : 0 < 1 / (beta * (1 + A * beta)) := by
    apply one_div_pos.mpr
    exact mul_pos hbeta hpos
  have hposg : 0 < closedLoopGain A beta := by
    unfold closedLoopGain
    exact div_pos hA hpos
  refine ⟨hposg, ?_⟩
  linarith

end PhyslibExt.Electronics.FiniteGainFeedback
