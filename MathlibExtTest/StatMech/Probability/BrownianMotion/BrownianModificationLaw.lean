/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianModificationLaw
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianModificationLaw`

* Existence of Brownian motion: `brownianContinuousModification_isStandardBrownianMotion`, and its
  consequences at concrete times: `B̃_1 = B_1` a.s., `B̃_0 = 0` a.s., continuous paths a.s.,
  `B̃_3 - B̃_1 ~ N(0, 2)`, independent increments over `[0, 1]`, `[2, 3]`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianModificationLaw

example : IsStandardBrownianMotion brownianContinuousModification brownianProductLaw :=
  brownianContinuousModification_isStandardBrownianMotion

example : brownianContinuousModification 1 =ᵐ[brownianProductLaw] brownianCoordinateProcess 1 :=
  brownianContinuousModification_ae_eq 1

example : ∀ᵐ ω ∂brownianProductLaw, brownianContinuousModification 0 ω = 0 :=
  brownianContinuousModification_start

example : ∀ᵐ ω ∂brownianProductLaw, Continuous (fun t => brownianContinuousModification t ω) :=
  brownianContinuousModification_continuous_paths

example : HasLaw (fun ω => brownianContinuousModification 3 ω - brownianContinuousModification 1 ω)
    (gaussianReal 0 2) brownianProductLaw := by
  have h := brownianContinuousModification_increment_law 1 3 (by norm_num)
  norm_num at h
  exact h

example : IndepFun
    (fun ω => brownianContinuousModification 1 ω - brownianContinuousModification 0 ω)
    (fun ω => brownianContinuousModification 3 ω - brownianContinuousModification 2 ω)
    brownianProductLaw :=
  brownianContinuousModification_indep_increments 0 1 2 3 (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianModificationLaw
