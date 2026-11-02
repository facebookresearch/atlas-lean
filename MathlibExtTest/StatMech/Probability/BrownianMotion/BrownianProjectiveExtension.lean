/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianProjectiveExtension
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianProjectiveExtension`

* `brownianProductLaw` is a probability measure whose marginal at `{0, 1}` is the Brownian
  finite-dimensional law (`brownianProductLaw_isProjectiveLimit`).
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianProjectiveExtension

example : IsProbabilityMeasure brownianProductLaw := inferInstance

example : brownianProductLaw.map (({0, 1} : Finset ℝ).restrict) =
    brownianFiniteDimensionalPiLaw {0, 1} := brownianProductLaw_isProjectiveLimit {0, 1}

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianProjectiveExtension
