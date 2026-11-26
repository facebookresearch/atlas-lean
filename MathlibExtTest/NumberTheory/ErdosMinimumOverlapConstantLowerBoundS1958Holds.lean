/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantLowerBoundS1958Holds

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantLowerBoundS1958Holds

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : (4 - Real.sqrt 6) / 5 ≤ C₁ᵦ := lowerBound_S1958_holds

-- Every strict threshold below Świerczkowski's bound is beaten by an actual translation.
example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) {c : ℝ}
    (hc : c < (4 - Real.sqrt 6) / 5) :
    ∃ x ∈ continuousTranslationInterval, c < continuousOverlap f g x := by
  have hscore : c < continuousPairScore f g :=
    (hc.trans_le lowerBound_S1958_holds).trans_le
      (continuousMinimumOverlapConstant_isUniversalLowerBound f g h)
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_lt_csSup (continuousOverlapValues_nonempty f g) hscore
  exact ⟨x, hx, hlt⟩

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantLowerBoundS1958Holds
