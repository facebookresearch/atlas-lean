/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantLowerBoundScherkUnpublished1955Holds

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantLowerBoundScherkUnpublished1955Holds

example : lowerBound_Scherk_unpublished_1955 = (1 - 1 / Real.sqrt 2 ≤ C₁ᵦ) := rfl

example : 1 - 1 / Real.sqrt 2 ≤ C₁ᵦ := lowerBound_Scherk_unpublished_1955_holds

example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) {c : ℝ}
    (hc : c < 1 - 1 / Real.sqrt 2) :
    ∃ x ∈ continuousTranslationInterval, c < continuousOverlap f g x := by
  have hscore : c < continuousPairScore f g :=
    (hc.trans_le lowerBound_Scherk_unpublished_1955_holds).trans_le
      (continuousMinimumOverlapConstant_isUniversalLowerBound f g h)
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_lt_csSup (continuousOverlapValues_nonempty f g) hscore
  exact ⟨x, hx, hlt⟩

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantLowerBoundScherkUnpublished1955Holds
