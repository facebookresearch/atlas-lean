/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.AffinePotentialMinimum
import Mathlib.Tactic.NormNum

/-!
# Affine-potential checks

Focused checks for
`MathlibExt.Analysis.Calculus.AffinePotentialMinimum`: the
zero potential with `α = 0` on the whole space, through the
bound.

These are elaboration and non-vacuity checks, not new results.
-/

/-- Zero potential at zero curvature bound. -/
example : (0 : ℝ) * ‖(1 : ℝ)‖ ^ 2 / 2
    ≤ (fun _ : ℝ => (0 : ℝ)) (0 + 1) - (fun _ : ℝ => (0 : ℝ)) 0 :=
  affine_potential_minimum_bound (⊤ : Submodule ℝ ℝ)
    («Π» := fun _ : ℝ => 0) (x0 := 0) (h := 1) (α := 0) (by simp)
    (by intro v _; simp [fderiv_const])
    (by intro t _; exact contDiff_const.contDiffAt)
    (by intro t _; simp [fderiv_const])
