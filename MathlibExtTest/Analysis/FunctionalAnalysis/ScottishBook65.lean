/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook65

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook65Wanted

-- Apply the refutation to the original claim with the symmetric hull written out.
example (claim : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : Set E), Convex ℝ W → 0 ∈ W → interior (closure W) = ∅ →
    interior (closure (convexHull ℝ (W ∪ {z | ∃ w ∈ W, z = -w}))) = ∅) :
    False :=
  mazur65_refuted claim
