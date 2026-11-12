/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.SingleIndexVariance
import Mathlib.Tactic.NormNum

/-!
# Tests for the single-index variance decomposition

* Non-vacuity test: `α = 3`, `β = 2` so `β ^ 2 = 4`, with `Var[RM; μ] ≠ 0` and
  `Var[ε; μ] ≠ 0` hypotheses certifying that the market and the residual both
  have nonzero variance. (A concrete `Fin 3` uniform-measure version was
  tried but its `PMF.uniformOfFintype` API does not compile under the repo's
  Mathlib v4.35.0.)
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.SingleIndexVariance

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Finance.SingleIndexVariance

set_option linter.unusedVariables false in
/-- Non-vacuity test (hypotheses version). The `Var ≠ 0` hypotheses certify
that the test instance is non-degenerate (the market and the residual both
have nonzero variance); they are part of the test's statement, not of the
main theorem. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (RM ε : Ω → ℝ) (hRM : MemLp RM 2 μ) (hε : MemLp ε 2 μ)
    (hCov : cov[RM, ε; μ] = 0)
    (hVarRM : Var[RM; μ] ≠ 0) (hVarε : Var[ε; μ] ≠ 0) :
    Var[singleIndexReturn 3 2 RM ε; μ] = 4 * Var[RM; μ] + Var[ε; μ] := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact singleIndex_variance_decomposition 3 2 RM ε hRM hε hCov

end MathlibExtTest.Probability.Finance.SingleIndexVariance
