/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.LebesgueUniversalCoveringConstant
import Mathlib.Tactic.NormNum
import MathlibExt.Geometry.LebesgueUniversalCoveringHansen

/-! # Sprague's bound for Lebesgue's covering problem

Sprague's upper bound follows from the stronger corrected bound of Hansen. Both decimal bounds
are stated in Section 1 of Baez, Bagdasaryan and Gibbs, *The Lebesgue universal covering problem*,
J. Comput. Geom. 6 (2015), 288–299.
-/

namespace MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

@[expose] public noncomputable section

/-- **Statement of Sprague's bound.** The proposition that the Lebesgue universal covering
constant is at most $0.844137708436$. -/
def sprague1936UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708436

/-- **Sprague's bound.** The Lebesgue universal covering constant is at most $0.844137708436$.

Source: Sprague, Über ein elementares Variationsproblem (1936). -/
theorem sprague1936UpperBound_holds : sprague1936UpperBound := by
  unfold sprague1936UpperBound
  calc
    lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708398 :=
      hansen1992CorrectedBBG2015UpperBound_holds
    _ ≤ ENNReal.ofReal 0.844137708436 := ENNReal.ofReal_le_ofReal (by norm_num)

end

end MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted
