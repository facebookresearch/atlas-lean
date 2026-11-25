/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook167Wanted

-- The negated claim must provide a family and a sphere map that work against every candidate
-- point, not a family or map that can be chosen after seeing the point.
example : ¬ (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    ¬ Module.Finite ℝ E →
    ∀ (n : ℕ) (f : Fin n → ↥(Metric.sphere (0 : E) 1) → ℝ)
      (T : ↥(Metric.sphere (0 : E) 1) → ↥(Metric.sphere (0 : E) 1)),
      Continuous T → (∀ i, Continuous (f i)) →
      ∃ p : ↥(Metric.sphere (0 : E) 1), ∀ i, f i (T p) = f i p) :=
  ulam167_refuted
