/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.IntegralFeedbackLoop
import Mathlib.Tactic.NormNum

/-! Exact numerical tests for the two-state integral-feedback loop. -/

open Matrix
open MathlibExt.Biology.Dynamics.IntegralFeedback
open MathlibExt.Biology.Dynamics.IntegralFeedbackLoop

private noncomputable def loop : LinearSystem (Fin 2) where
  A := !![-2, -3; 1, 0]
  b := ![1, 0]
  c := ![1, 0]
  d := 0

example : loop.field ![4, 5] 7 0 = -16 ∧ loop.field ![4, 5] 7 1 = 4 ∧
    loop.output ![4, 5] 7 = 4 ∧ loop.A.det = 3 := by
  obtain ⟨hcoords, hdet, _, _, _, _⟩ :=
    integral_feedback_loop_equilibrium_and_dc_gain (a := 2) (b := 3) (by norm_num) (by norm_num)
  obtain ⟨h₀, h₁, hy⟩ := hcoords ![4, 5] 7
  refine ⟨?_, h₁, hy, hdet⟩
  calc
    _ = -(2 : ℝ) * 4 - 3 * 5 + 7 := h₀
    _ = -16 := by norm_num

example : (∀ x, loop.field x 0 = 0 ↔ x = ![0, 0]) ∧ loop.output ![0, 0] 0 = 0 := by
  obtain ⟨_, _, _, heq, hout, _⟩ :=
    integral_feedback_loop_equilibrium_and_dc_gain (a := 2) (b := 3) (by norm_num) (by norm_num)
  exact ⟨fun x ↦ by simpa [loop] using heq x 0, by simpa [loop] using hout 0⟩

example : (∃! x, loop.field x (-5) = 0) ∧ loop.field ![0, -5 / 3] (-5) = 0 ∧
    loop.output ![0, -5 / 3] (-5) = 0 ∧ loop.dcGain = 0 := by
  obtain ⟨_, _, _, heq, hout, hgain⟩ :=
    integral_feedback_loop_equilibrium_and_dc_gain (a := 2) (b := 3) (by norm_num) (by norm_num)
  have h := (heq ![0, -5 / 3] (-5)).2 rfl
  exact ⟨⟨_, h, fun x hx ↦ (heq x (-5)).1 hx⟩, h, hout (-5), hgain⟩
