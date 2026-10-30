/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.CanonicalBrownianLaw
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.CanonicalBrownianLaw`

* `brownianContinuousModification_processLaw`: the path law of the canonical Brownian motion is
  `brownianProductLaw`.
* `brownianContinuousModification_isBrownianReal`: a process satisfying Mathlib's `IsBrownianReal`
  exists; Mathlib's API then gives `B 2 ~ N(0, 2)`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.CanonicalBrownianLaw

example : brownianProductLaw.map (fun ω t => brownianContinuousModification t ω) =
    brownianProductLaw := brownianContinuousModification_processLaw

example : HasLaw (brownianContinuousModification (2 : ℝ≥0)) (gaussianReal 0 2) brownianProductLaw :=
  brownianContinuousModification_isBrownianReal.hasLaw_eval 2

end MathlibExtTest.StatMech.Probability.BrownianMotion.CanonicalBrownianLaw
