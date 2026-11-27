/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.HeldDACSettling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.Instrumentation.DACLevelError
open PhyslibExt.Instrumentation.HeldDACSettling

namespace PhyslibExtTest.Instrumentation.HeldDACSettling

/-- At zero elapsed time the settling output is the initial
value, with exponential factor one: `settlingOutput 5 2 3 7 3`
is `2`, and its deviation from the held level `5` is the initial
mismatch `-3` times `exp 0`. -/
example : settlingOutput 5 2 3 7 3 = 2 ∧
    settlingOutput 5 2 3 7 3 - 5 =
      (2 - 5) * Real.exp (-(3 - 3 : ℝ) / 7) := by
  constructor
  · exact settlingOutput_at_start 5 2 3 7
  · simp [settlingOutput]

/-- Positive elapsed time fixes the sign and the scaling of the
exponent: after `2` time units with `tau = 2` the factor is
`exp (-1)`, not `exp (-2)` or `exp 1`, so the output starting at
`2` has moved strictly toward the held level `5` without reaching
it. -/
example : settlingOutput 5 2 0 2 2 = 5 - 3 * Real.exp (-1) ∧
    2 < settlingOutput 5 2 0 2 2 ∧ settlingOutput 5 2 0 2 2 < 5 := by
  have hval : settlingOutput 5 2 0 2 2 = 5 - 3 * Real.exp (-1) := by
    simp only [settlingOutput]
    norm_num
    ring
  have hpos : 0 < Real.exp (-1) := Real.exp_pos _
  have hlt : Real.exp (-1) < 1 := by simp
  refine ⟨hval, ?_, ?_⟩ <;> rw [hval] <;> linarith

/-- A concrete solution of `2 * y' = 5 - y` starting at `2` at
time `0`. -/
noncomputable def fixtureOutput (s : ℝ) : ℝ :=
  5 - 3 * Real.exp (-s / 2)

lemma fixtureOutput_hasDerivAt (s : ℝ) :
    HasDerivAt fixtureOutput (3 / 2 * Real.exp (-s / 2)) s := by
  have hinner : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) s :=
    (hasDerivAt_neg s).div_const 2
  exact ((hinner.exp.const_mul 3).const_sub 5).congr_deriv (by ring)

lemma fixtureOutput_ode (s : ℝ) :
    2 * deriv fixtureOutput s = 5 - fixtureOutput s := by
  rw [(fixtureOutput_hasDerivAt s).deriv]
  unfold fixtureOutput
  ring

lemma fixtureOutput_continuousOn (a b : ℝ) :
    ContinuousOn fixtureOutput (Set.Icc a b) :=
  fun s _ => (fixtureOutput_hasDerivAt s).continuousAt.continuousWithinAt

lemma fixtureOutput_differentiableAt (s : ℝ) :
    DifferentiableAt ℝ fixtureOutput s :=
  (fixtureOutput_hasDerivAt s).differentiableAt

lemma fixtureOutput_zero : fixtureOutput 0 = 2 := by
  simp only [fixtureOutput]
  norm_num

/-- The interval results on a nonzero-length interval `[0, 2]`
with `tau = 2`: the endpoint recurrence gives `5 - 3 * exp (-1)`,
and the settling error at the endpoint is `3 * exp (-1)`,
strictly below the initial mismatch `3`. -/
example : fixtureOutput 2 = 5 - 3 * Real.exp (-1) ∧
    |fixtureOutput 2 - 5| = 3 * Real.exp (-1) ∧
    |fixtureOutput 2 - 5| < |fixtureOutput 0 - 5| := by
  have hend := heldOutput_endpoint_recurrence 2 5 0 2 (by norm_num) (by norm_num)
    fixtureOutput (fixtureOutput_continuousOn 0 2)
    (fun s _ => fixtureOutput_differentiableAt s) (fun s _ => fixtureOutput_ode s)
  have herr := settlingError_eq 2 5 0 2 (by norm_num) (by norm_num)
    fixtureOutput (fixtureOutput_continuousOn 0 2)
    (fun s _ => fixtureOutput_differentiableAt s) (fun s _ => fixtureOutput_ode s)
    2 ⟨by norm_num, le_rfl⟩
  have harg : (-(2 - 0) / 2 : ℝ) = -1 := by norm_num
  have habs : |(2 : ℝ) - 5| = 3 := by norm_num [abs_of_neg]
  rw [fixtureOutput_zero, harg] at hend herr
  rw [habs] at herr
  have hlt : Real.exp (-1) < 1 := by simp
  refine ⟨by rw [hend]; ring, herr, ?_⟩
  rw [herr, fixtureOutput_zero, habs]
  linarith

/-- Code-held settling on `[0, 2]`: the code `2` with step `2`
and constant error `1` has actual level `5`, so the fixture
settles toward that level and its error at the endpoint is
`3 * exp (-1)`. -/
example : |fixtureOutput 2 - dacLevel 2 (fun _ => 1) 2| = 3 * Real.exp (-1) := by
  have hlevel : dacLevel 2 (fun _ => 1) 2 = 5 := by
    simp only [dacLevel]
    norm_num
  have h := codeHeld_settlingError_eq 2 2 (by norm_num) (fun _ => 1) 2 0 2 (by norm_num)
    fixtureOutput (fixtureOutput_continuousOn 0 2)
    (fun s _ => fixtureOutput_differentiableAt s)
    (fun s _ => by rw [hlevel]; exact fixtureOutput_ode s)
    2 ⟨by norm_num, le_rfl⟩
  rw [h, hlevel, fixtureOutput_zero]
  norm_num [abs_of_neg]

end PhyslibExtTest.Instrumentation.HeldDACSettling
