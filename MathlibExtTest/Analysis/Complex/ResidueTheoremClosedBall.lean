/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.ResidueTheoremClosedBall
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Analysis.Complex.ResidueTheoremClosedBall` -/

open scoped BigOperators Real
open Metric Set Complex
open MathlibExt.Analysis.Complex.ResidueTheoremWanted

namespace MathlibExtTest.Analysis.Complex.ResidueTheoremClosedBall

-- The residue theorem applied to `z ↦ z⁻¹` with the single singularity `0`: both circle
-- integrals are `2πi`.
example : (∮ z in C((0 : ℂ), 2), z⁻¹) = 2 * π * I := by
  have hcont : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) 2) := by
    refine ContinuousOn.inv₀ continuousOn_id fun z hz => ?_
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact fun h => by rw [h] at hz; simp at hz
  have hcont1 : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) 1) := by
    refine ContinuousOn.inv₀ continuousOn_id fun z hz => ?_
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact fun h => by rw [h] at hz; simp at hz
  have hf : DifferentiableOn ℂ (fun z : ℂ => z⁻¹)
      (Metric.closedBall (0 : ℂ) 2 \ ↑({0} : Finset ℂ)) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      exact hz.2 (by simp [h])
    exact (differentiableAt_inv hz0).differentiableWithinAt
  have h := residueTheorem_closedBall (c := (0 : ℂ)) (R := 2) (f := fun z : ℂ => z⁻¹)
    (S := {0}) (rad := fun _ => 1) (by norm_num)
    (by
      intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      exact Metric.mem_ball_self (by norm_num))
    (by
      intro s hs
      simp only [Finset.mem_singleton] at hs
      subst hs
      refine ⟨by norm_num, ?_, ?_⟩
      · intro w hw
        exact Metric.mem_ball.2
          (lt_of_le_of_lt (Metric.mem_closedBall.1 hw) (by norm_num))
      · intro s' hs' hne hw
        rw [Finset.mem_singleton] at hs'
        subst hs'
        exact absurd rfl hne)
    hf
    (hcont.circleIntegrable (by norm_num))
    (by
      intro s hs
      simp only [Finset.mem_singleton] at hs
      subst hs
      exact hcont1.circleIntegrable (by norm_num))
  rw [Finset.sum_singleton] at h
  rw [h]
  have h1 := circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := (0 : ℂ))
    (R := 1) (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  simp only [sub_zero] at h1
  exact h1

-- The empty-singularity case: the circle integral of the constant function `1` is `0`.
example : (∮ _ in C((0 : ℂ), 2), (1 : ℂ)) = 0 := by
  have h := residueTheorem_closedBall (c := (0 : ℂ)) (R := 2) (f := fun _ => (1 : ℂ))
    (S := (∅ : Finset ℂ)) (rad := fun _ => 1) (by norm_num) (by simp)
    (by intro s hs; simp at hs) (differentiableOn_const 1)
    (circleIntegrable_const 1 (0 : ℂ) 2) (by simp)
  simpa using h

end MathlibExtTest.Analysis.Complex.ResidueTheoremClosedBall
