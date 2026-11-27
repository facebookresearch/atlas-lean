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

open HauglandFifteenStep

-- The overlap of Haugland's 15-step pair at the six-cell shift `x = 4 / 5`, where its grid
-- overlaps peak.
private theorem overlap_sixCells :
    continuousOverlap (profile weight) (profile complement) (4 / 5) =
      4769144353094739 / 12500000000000000 := by
  have h := overlap_grid 6
  norm_num [Finset.sum_range_succ, weight] at h
  exact h

-- Hence the pair scores above `0.38153154`, consistent with the value `0.38153155` (rounded up)
-- that Haugland reports: this witness alone certifies no smaller bound.
example : (38153154 : ℝ) / 10 ^ 8 < continuousPairScore (profile weight) (profile complement) :=
  lt_of_lt_of_le (by norm_num) (le_csSup admissible.overlapValues_bddAbove
    ⟨4 / 5, by norm_num [continuousTranslationInterval], overlap_sixCells⟩)
