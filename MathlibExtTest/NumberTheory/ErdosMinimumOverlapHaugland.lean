/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapHaugland

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : C₁ᵦ ≤ (382002 : ℝ) / 1000000 := upperBound_H1996_holds

-- Every threshold strictly above the bound fails on an admissible pair.
example {c : ℝ} (hc : (382002 : ℝ) / 1000000 < c) :
    ∃ f g, ContinuousAdmissible f g ∧ continuousPairScore f g < c := by
  by_contra! h
  have hbound : c ∈ continuousValidLowerBounds := h
  exact (not_lt_of_ge (continuousMinimumOverlapConstant_isGreatest.2 hbound))
    (lt_of_le_of_lt upperBound_H1996_holds hc)
