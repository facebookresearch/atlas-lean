/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.SupOnTangentCirclesLogConvex
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MathlibExt.Analysis.Complex.SupOnTangentCirclesLogConvexWanted

-- For the identity function the maximum of the norm on the tangent circle is `2 * r`.
example : (2 : ℝ) ^ 2 ≤ (2 * 2) * (2 * (2 / 3)) := by
  have h := sq_sSup_norm_circle_one_le_mul id differentiable_id (fun r => 2 * r) (fun r hr => by
    have hnr : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
    have hn2r : ‖((2 * r : ℝ) : ℂ)‖ = 2 * r := by
      simp [hr.le]
    symm
    apply IsGreatest.csSup_eq
    refine ⟨⟨((2 * r : ℝ) : ℂ), ?_, hn2r.symm⟩, ?_⟩
    · have heq : ((2 * r : ℝ) : ℂ) - (r : ℂ) = (r : ℂ) := by push_cast; ring
      rw [heq, hnr]
    · rintro t ⟨z, hz, rfl⟩
      change ‖z‖ ≤ 2 * r
      calc
        ‖z‖ = ‖(z - (r : ℂ)) + (r : ℂ)‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - (r : ℂ)‖ + ‖(r : ℂ)‖ := norm_add_le _ _
        _ = 2 * r := by rw [hz, hnr, two_mul])
  simpa only [mul_one] using h
