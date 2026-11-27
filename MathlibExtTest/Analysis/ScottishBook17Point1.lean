/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScottishBook17Point1
import Mathlib.Analysis.Calculus.TangentCone.DimOne
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Tests for Ulam's perfect set problem -/

open MathlibExt.Analysis.ScottishBook17Point1Wanted Set
open scoped ContDiff Topology

-- The refutation gives a single continuous function that defeats every analytic candidate.
example : ∃ f : ℝ → ℝ, ContinuousOn f (Icc (0 : ℝ) 1) ∧
    ∀ (C : Set ℝ) (φ : ℝ → ℝ), IsPerfectSet C → C ⊆ Icc (0 : ℝ) 1 →
      AnalyticOn ℝ φ (Icc (0 : ℝ) 1) → ∃ x ∈ C, f x ≠ φ x := by
  classical
  obtain ⟨f, hf⟩ := not_forall.mp continuousFunctionPerfectAnalytic_refuted
  obtain ⟨hcont, hno⟩ := not_imp.mp hf
  refine ⟨f, hcont, fun C φ hC hCI hφ => ?_⟩
  by_contra! heq
  exact hno ⟨C, φ, hC, hCI, hφ, heq⟩

-- A single globally smooth witness rules out agreement on any nonempty perfect subset.
example : ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧
    ∀ C ⊆ Icc (0 : ℝ) 1, IsPerfectSet C → ∀ φ : ℝ → ℝ,
      AnalyticOn ℝ φ (Icc (0 : ℝ) 1) → ¬ C.EqOn f φ := by
  obtain ⟨f, hf⟩ := not_forall.mp smoothFunctionPerfectAnalytic_refuted
  obtain ⟨hsmooth, hno⟩ := not_imp.mp hf
  exact ⟨f, hsmooth, fun C hCI hC φ hφ heq => hno ⟨C, φ, hC, hCI, hφ, fun _ hx => heq hx⟩⟩

-- Both endpoints satisfy the accumulation-point condition for the full interval.
example : IsPerfectSet (Icc (0 : ℝ) 1) := by
  refine ⟨isClosed_Icc, nonempty_Icc.2 zero_le_one, fun x hx => ?_⟩
  rw [mem_closure_iff_nhdsWithin_neBot, ← accPt_principal_iff_nhdsWithin,
    ← uniqueDiffWithinAt_iff_accPt]
  exact uniqueDiffOn_Icc zero_lt_one x hx
