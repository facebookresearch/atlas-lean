/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook7

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook7Wanted
  (ScottishBookProblem7Claim closedConvexSetsHomeomorphic_refuted)

/-- The proved claim retains all the original quantifiers. -/
example : ¬ (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A B : Set E), IsClosed A → Convex ℝ A →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ A) → IsClosed B → Convex ℝ B →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ B) → Nonempty (↥A ≃ₜ ↥B)) :=
  closedConvexSetsHomeomorphic_refuted
