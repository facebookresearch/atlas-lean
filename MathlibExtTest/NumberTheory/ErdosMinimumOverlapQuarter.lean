/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapQuarter

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : (1 : ℝ) / 4 ≤ C₁ᵦ := lowerBound_E1955_quarter_holds

-- Every strict lower threshold is beaten by an actual translation.
example {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) {c : ℝ} (hc : c < 1 / 4) :
    ∃ x ∈ continuousTranslationInterval, c < continuousOverlap f g x := by
  have hscore : c < continuousPairScore f g :=
    (hc.trans_le lowerBound_E1955_quarter_holds).trans_le
      (continuousMinimumOverlapConstant_isUniversalLowerBound f g h)
  obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
    exists_lt_of_lt_csSup (continuousOverlapValues_nonempty f g) hscore
  exact ⟨x, hx, hlt⟩
