/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.RenderingEquation

/-! # Examples for the rendering equation -/

open scoped ENNReal
open ContinuousLinearMap

-- With no transport, emission is the unique solution and is the sum of the series.
example : HasSum (fun k : ℕ => ((0 : ℝ →L[ℝ] ℝ) ^ k) 2) 2 ∧
    (∀ J : ℝ, J = 2 + (0 : ℝ →L[ℝ] ℝ) J ↔ J = 2) := by
  obtain ⟨hs, hfix, _⟩ := rendering_equation_fixed_point_and_counterexample.1
    (0 : ℝ →L[ℝ] ℝ) 0 (by simp) zero_lt_one 2
  have hsum : (∑' k : ℕ, ((0 : ℝ →L[ℝ] ℝ) ^ k) 2) = 2 :=
    ((hfix 2).mp (by simp)).symm
  rw [hsum] at hs hfix
  exact ⟨hs, hfix⟩

-- The diagonal counterexample kills coordinate zero but still has no bounded solution.
example : ∃ (T : lp (fun _ : ℕ => ℝ) ⊤ →L[ℝ] lp (fun _ : ℕ => ℝ) ⊤)
    (E : lp (fun _ : ℕ => ℝ) ⊤),
    (∀ x, (T x : ℕ → ℝ) 0 = 0) ∧ ‖T‖ = 1 ∧ ¬ ∃ I, I = E + T I := by
  obtain ⟨T, E, hdiag, _, hnorm, hnosol⟩ := rendering_equation_fixed_point_and_counterexample.{0}.2
  exact ⟨T, E, fun x => by simpa using hdiag x 0, hnorm, hnosol⟩
