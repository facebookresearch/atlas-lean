/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapMoser

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : lowerBound_M1959 = (Real.sqrt (4 - Real.sqrt 15) ≤ C₁ᵦ) := rfl

example : Real.sqrt (4 - Real.sqrt 15) ≤ C₁ᵦ := lowerBound_M1959_holds

-- A threshold strictly below Moser's bound is exceeded by some overlap value.
example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) {c : ℝ}
    (hc : c < Real.sqrt (4 - Real.sqrt 15)) :
    ∃ x ∈ continuousTranslationInterval, c < continuousOverlap f g x := by
  have hscore : c < continuousPairScore f g :=
    (hc.trans_le lowerBound_M1959_holds).trans_le
      (continuousMinimumOverlapConstant_isUniversalLowerBound f g h)
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_lt_csSup (continuousOverlapValues_nonempty f g) hscore
  exact ⟨x, hx, hlt⟩
