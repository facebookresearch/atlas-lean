/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook91

/-! # Statement test for Mazur's Problem 91 -/

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook91Wanted (mazur91_refuted)

universe u

/-- The public theorem refutes the original claim in an arbitrary universe. -/
example : ¬ (∀ (n : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E],
    Module.finrank ℝ E = n →
    (∃ _ : E ≃ₗᵢ[ℝ] StrongDual ℝ E, True) →
    ∃ _ : InnerProductSpace ℝ E, True) :=
  mazur91_refuted
