/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Mechanics.EulerBernoulliBeam

/-!
# Uniform-load beam witness checks

Focused checks for `PhyslibExt.Mechanics.EulerBernoulliBeam` at
`L = 4`, `EI = 2`, `w = 3`: the deflection vanishes at both supports,
the second derivative vanishes at both supports, `EI * y'''' = 3`, and
the midspan deflection is the textbook value `5`.

These are elaboration and non-vacuity checks, not new results.
-/

open Mechanics.EulerBernoulli

/-- Support deflections at the witness data. -/
example : uniformLoadDeflection 3 2 4 0 = 0 ∧ uniformLoadDeflection 3 2 4 4 = 0 :=
  ⟨uniformLoadDeflection_zero_left 3 2 4, uniformLoadDeflection_zero_right 3 2 4⟩

/-- End moments vanish at the witness data. -/
example : iteratedDeriv 2 (uniformLoadDeflection 3 2 4) 0 = 0
    ∧ iteratedDeriv 2 (uniformLoadDeflection 3 2 4) 4 = 0 :=
  ⟨uniformLoadDeflection_secondDeriv_zero_left 3 2 4,
    uniformLoadDeflection_secondDeriv_zero_right 3 2 4⟩

/-- The load equation at the witness data. -/
example (x : ℝ) : 2 * iteratedDeriv 4 (uniformLoadDeflection 3 2 4) x = 3 :=
  uniformLoadDeflection_ei_mul_iteratedDeriv_four 3 2 4 (by norm_num) x

/-- Midspan deflection is `5`. -/
example : uniformLoadDeflection 3 2 4 2 = 5 := by
  norm_num [uniformLoadDeflection]

/-- Zero load gives the zero witness. -/
example (x : ℝ) : uniformLoadDeflection 0 2 4 x = 0 := by
  norm_num [uniformLoadDeflection]
