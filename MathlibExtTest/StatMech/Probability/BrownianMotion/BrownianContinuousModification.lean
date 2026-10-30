/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianContinuousModification
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianContinuousModification`

* `brownianCompactRadius` at `t = -5/2` is `3`, and the window contains `t`.
* `brownianContinuousModification_eq_dyadicLimit` at `t = 1/2` in the window `N = 2`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianContinuousModification

example : brownianCompactRadius (-5 / 2) = 3 := by
  simp [brownianCompactRadius]
  norm_num [Nat.ceil_eq_iff]

example : -(brownianCompactRadius (-5 / 2) : ℝ) ≤ -5 / 2 ∧ (-5 / 2 : ℝ) ≤ brownianCompactRadius (-5 / 2) :=
  ⟨neg_brownianCompactRadius_le _, le_brownianCompactRadius _⟩

example (ω : ℝ → ℝ) : brownianContinuousModification (1 / 2) ω = brownianDyadicLimit 2 (1 / 2) ω :=
  brownianContinuousModification_eq_dyadicLimit ω 2 (by norm_num) (by norm_num)

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianContinuousModification
