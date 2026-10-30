/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.StandardBrownianLaw
public import MathlibExt.Probability.BrownianMotion.BrownianModificationLaw
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.StandardBrownianLaw`

* The `IsStandardBrownianMotion` API applied to the canonical Brownian motion: `E B̃_2 = 0`,
  `Var B̃_{-3} = 3`, `Cov(B̃_1, B̃_2) = 1`, `Cov(B̃_{-1}, B̃_1) = 0`.
* `standardBrownian_processLaw_eq` (with itself) and the bridges `isBrownianReal`,
  `hasIndepIncrements_nnreal` to Mathlib.
* The witness is the canonical Brownian motion from `BrownianModificationLaw` (extra import).
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.StandardBrownianLaw

/-- The canonical Brownian motion. -/
theorem hB : IsStandardBrownianMotion brownianContinuousModification brownianProductLaw :=
  brownianContinuousModification_isStandardBrownianMotion

example : (∫ ω, brownianContinuousModification 2 ω ∂brownianProductLaw) = 0 := hB.integral_eq_zero 2

example : Var[brownianContinuousModification (-3); brownianProductLaw] = 3 := by
  rw [hB.variance_eq_abs]; norm_num

example : cov[brownianContinuousModification 1, brownianContinuousModification 2;
    brownianProductLaw] = 1 := by
  rw [hB.covariance_eq]; norm_num

example : cov[brownianContinuousModification (-1), brownianContinuousModification 1;
    brownianProductLaw] = 0 := by
  rw [hB.covariance_eq]; norm_num

example : brownianProductLaw.map (fun ω t => brownianContinuousModification t ω) =
    brownianProductLaw.map (fun ω t => brownianContinuousModification t ω) :=
  standardBrownian_processLaw_eq hB hB

example : IsBrownianReal (fun (t : ℝ≥0) ω => brownianContinuousModification t ω)
    brownianProductLaw := hB.isBrownianReal

example : HasIndepIncrements (fun (t : ℝ≥0) ω => brownianContinuousModification t ω)
    brownianProductLaw := hB.hasIndepIncrements_nnreal

end MathlibExtTest.StatMech.Probability.BrownianMotion.StandardBrownianLaw
