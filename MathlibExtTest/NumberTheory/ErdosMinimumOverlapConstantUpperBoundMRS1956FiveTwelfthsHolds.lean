/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantUpperBoundMRS1956FiveTwelfthsHolds

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundMRS1956FiveTwelfthsHolds

example : C₁ᵦ ≤ (5 : ℝ) / 12 := upperBound_MRS1956_fiveTwelfths_holds

-- Above 5/12 no universal lower bound can lie: some admissible pair scores below c.
example {c : ℝ} (hc : (5 : ℝ) / 12 < c) :
    ∃ f g, ContinuousAdmissible f g ∧ continuousPairScore f g < c := by
  by_contra! hcon
  have hmem : c ∈ continuousValidLowerBounds := hcon
  have hle : c ≤ C₁ᵦ := by
    apply continuousMinimumOverlapConstant_isGreatest.2
    exact hmem
  have hub : C₁ᵦ ≤ (5 : ℝ) / 12 := upperBound_MRS1956_fiveTwelfths_holds
  linarith

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundMRS1956FiveTwelfthsHolds
