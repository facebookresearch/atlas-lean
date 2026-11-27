/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Mechanics.EulerBernoulliBeamDiagrams

/-!
# Beam diagram checks

Focused checks for
`PhyslibExt.Mechanics.EulerBernoulliBeamDiagrams`: at load
`w = 3`, span `L = 4`, and unit rigidity, the midpoint moment is
`6`, the end shears are `6` and `-6`, and the end moments
vanish, and the equilibrium law gives shear derivative `-3`.

These are elaboration and non-vacuity checks, not new results.
-/

open Mechanics.EulerBernoulli

/-- Midpoint moment value at the concrete witness. -/
example : uniformBeamMoment 3 1 4 2 = 6 := by
  have h := (uniformBeamMoment_midpoint_max (w := 3) (EI := 1) (L := 4)
    (by norm_num) (by norm_num) (by norm_num)).1
  norm_num at h ⊢
  exact h

/-- The midpoint belongs to the span at the concrete witness. -/
example : (4 : ℝ) / 2 ∈ Set.Icc 0 4 :=
  (uniformBeamMoment_midpoint_max (w := 3) (EI := 1) (L := 4)
    (by norm_num) (by norm_num) (by norm_num)).2.1

/-- End moments and end shears at the concrete witness. -/
example : uniformBeamMoment 3 1 4 0 = 0
    ∧ uniformBeamMoment 3 1 4 4 = 0
    ∧ uniformBeamShear 3 1 4 0 = 6
    ∧ uniformBeamShear 3 1 4 4 = -6 := by
  obtain ⟨h1, h2, h3, h4, _⟩ :=
    uniformBeam_endpoints (w := 3) (EI := 1) (L := 4) (by norm_num)
  refine ⟨h1, h2, ?_, ?_⟩ <;> norm_num at h3 h4 ⊢ <;> assumption

/-- End moments need no rigidity nondegeneracy hypothesis. -/
example : uniformBeamMoment 3 0 4 0 = 0
    ∧ uniformBeamMoment 3 0 4 4 = 0 :=
  ⟨uniformBeamMoment_zero, uniformBeamMoment_at_right⟩

/-- Equilibrium law at the concrete witness, through the
standalone theorem. -/
example : deriv (uniformBeamShear 3 1 4) = fun _ => -(3 : ℝ) :=
  uniformBeamShear_deriv (by norm_num)
