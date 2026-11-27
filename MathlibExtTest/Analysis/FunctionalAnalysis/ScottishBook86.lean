/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86

open MeasureTheory
open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted

-- Keep the ambient measure and the original same-bound proposition reducible to their statements.
example : scottishBook86Measure = volume.restrict (Set.Icc (0 : ℝ) 1) := rfl

example : ScottishBookProblem86Claim =
    (∀ (M : ℝ) (φ : ℕ → ℝ → ℝ), 0 < M →
      (∀ n, AEStronglyMeasurable (φ n) scottishBook86Measure) →
      (∀ n m, ∫ t, φ n t * φ m t ∂scottishBook86Measure = if n = m then 1 else 0) →
      (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |φ n t| ≤ M) →
      ∃ ψ : ℕ → ℝ → ℝ,
        (∀ n, AEStronglyMeasurable (ψ n) scottishBook86Measure) ∧
        (∀ n m, ∫ t, ψ n t * ψ m t ∂scottishBook86Measure = if n = m then 1 else 0) ∧
        (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |ψ n t| ≤ M) ∧
        (∀ n, ∃ m, ψ m = φ n) ∧
        ∀ g : ℝ → ℝ, MemLp g 2 scottishBook86Measure →
          (∀ n, ∫ t, ψ n t * g t ∂scottishBook86Measure = 0) →
          g =ᵐ[scottishBook86Measure] 0) := rfl

example : ¬ ScottishBookProblem86Claim := banach86_refuted
