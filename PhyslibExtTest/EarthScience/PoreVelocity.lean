/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.PoreVelocity

/-!
# Pore-velocity checks

Focused checks for `PhyslibExt.EarthScience.PoreVelocity`: a
quarter porosity quadruples a unit Darcy discharge, and the
corresponding Courant number at `dt = 1`, `dx = 2` is `2`.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Quarter porosity quadruples the speed. -/
example : poreVelocity 2 (1 / 4) = 8 := by
  rw [poreVelocity_quarter]
  norm_num

/-- Round trip back to the Darcy discharge. -/
example : poreVelocity 2 (1 / 4) * (1 / 4) = 2 :=
  poreVelocity_mul (by norm_num)

/-- A nonzero Courant number. -/
example : courantNumber 1 (1 / 4) 1 2 = 2 := by
  unfold courantNumber
  norm_num

/-- Nonnegativity and the zero-step case at the same witness. -/
example : 0 ≤ courantNumber 1 (1 / 4) 1 2
    ∧ courantNumber 1 (1 / 4) 0 2 = 0 :=
  ⟨courantNumber_nonneg (by norm_num) (by norm_num),
    courantNumber_zero_dt _ _ _⟩
