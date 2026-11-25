/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.UnimodularBoundaryImageContainsDisc
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.NormNum

/-! # Tests for the image of a holomorphic function with unimodular boundary values -/

open Metric Set
open MathlibExt.Analysis.Complex.UnimodularBoundaryImageContainsDiscWanted

-- Squaring on the radius-two disc covers every interior value, including the critical value zero.
example {w : ℂ} (hw : ‖w‖ < 1) : ∃ z ∈ ball (0 : ℂ) 2, z ^ 2 = w := by
  apply ball_subset_image_of_norm_eq_one_on_sphere (f := fun z ↦ z ^ 2) isOpen_ball
    (convex_ball _ _).isPreconnected (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
    (differentiable_id.pow 2).differentiableOn _ _ (mem_ball_zero_iff.mpr hw)
  · exact ⟨0, mem_ball_self zero_lt_two, 1, by norm_num [mem_ball_zero_iff], by norm_num⟩
  · intro z hz
    simp [norm_pow, mem_sphere_zero_iff_norm.mp hz]

-- Removing the radius-two circle lets a holomorphic function take different constants on
-- the two components. The unit circle still maps to the unit circle, yet zero is omitted.
open scoped Classical in
example :
    let U := ball (0 : ℂ) 2 ∪ (closedBall 0 2)ᶜ
    let f : ℂ → ℂ := fun z ↦ if z ∈ ball (0 : ℂ) 2 then 1 else -1
    IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ f U ∧
      (∃ x ∈ U, ∃ y ∈ U, f x ≠ f y) ∧
      (∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ = 1) ∧ 0 ∉ f '' U := by
  intro U f
  have hdisc : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  refine ⟨isOpen_ball.union isClosed_closedBall.isOpen_compl, hdisc.trans subset_union_left,
    ?_, ?_, ?_, ?_⟩
  · apply DifferentiableOn.union_of_isOpen _ _ isOpen_ball isClosed_closedBall.isOpen_compl
    · exact (differentiableOn_const 1).congr fun z hz ↦ ite_eq_left hz
    · exact (differentiableOn_const (-1)).congr fun z hz ↦
        ite_eq_right (fun h ↦ hz (ball_subset_closedBall h))
  · refine ⟨0, Or.inl (mem_ball_self zero_lt_two), 3, Or.inr ?_, ?_⟩
    · norm_num [mem_closedBall_zero_iff]
    · norm_num [f, mem_ball_zero_iff]
  · intro z hz
    simp only [f, ite_eq_left (hdisc (sphere_subset_closedBall hz)), norm_one]
  · rintro ⟨z, _, hz⟩
    dsimp only [f] at hz
    split at hz <;> norm_num at hz
