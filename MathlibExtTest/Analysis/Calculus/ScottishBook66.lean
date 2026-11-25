/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.ScottishBook66

/-! # Scottish Book Problem 66 regression -/

open MathlibExt.Analysis.Calculus.ScottishBook66Wanted MeasureTheory

-- Unpack the refutation into a counterexample for the specified derivative order and measure.
example : ∃ f : ℝ × ℝ → ℝ,
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun t ↦ f (t, y)) x) ∧
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun t ↦ f (x, t)) y) ∧
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun t ↦ f (t, y))) x) ∧
    (∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      DifferentiableAt ℝ (deriv (fun t ↦ f (x, t))) y) ∧
    0 < (volume.restrict (Set.Ioo (0, 0) (1, 1) : Set (ℝ × ℝ)))
      {p | ¬ DifferentiableAt ℝ (fun t ↦ deriv (fun s ↦ f (t, s)) p.2) p.1} := by
  classical
  have h := mazur66_refuted
  simp only [ScottishBookProblem66Claim, not_forall, ae_iff] at h
  obtain ⟨f, hx, hy, hxx, hyy, hfail⟩ := h
  exact ⟨f, hx, hy, hxx, hyy, pos_iff_ne_zero.mpr hfail⟩
