/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianMomentBound
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianMomentBound`

* `integral_pow_four_gaussianReal`: the fourth moment of `N(0, 1)` is `3` and of `N(0, 2)` is `12`.
* `brownianFiniteDimensionalPiLaw_isKolmogorovProcess` at `I = {0, 1}`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianMomentBound

example : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  simpa using integral_pow_four_gaussianReal 1

example : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 2) = 12 := by
  rw [integral_pow_four_gaussianReal]; norm_num

example : IsKolmogorovProcess (fun t : ({0, 1} : Finset ℝ) ↦ fun x : ({0, 1} : Finset ℝ) → ℝ ↦ x t)
    (brownianFiniteDimensionalPiLaw {0, 1}) 4 2 3 :=
  brownianFiniteDimensionalPiLaw_isKolmogorovProcess _

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianMomentBound
