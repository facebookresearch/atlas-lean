/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.PortfolioBeta
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for portfolio beta

* Application test: a two-asset portfolio with weights `1/3` and `2/3` has
  beta `(1/3) * β_0 + (2/3) * β_1`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.PortfolioBeta

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Finance.PortfolioBeta

/-- Application test: two-asset portfolio with weights `1/3` and `2/3`. -/
theorem portfolio_beta_two_asset_test
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Fin 2 → Ω → ℝ) (RM : Ω → ℝ)
    (hR : ∀ i, MemLp (R i) 2 μ) (hM : MemLp RM 2 μ)
    (hVar : 0 < Var[RM; μ]) :
    assetBeta μ (fun ω => ∑ i, ![1/3, 2/3] i * R i ω) RM =
      (1/3) * assetBeta μ (R 0) RM + (2/3) * assetBeta μ (R 1) RM := by
  have h := portfolio_beta_linear R RM ![1/3, 2/3] hR hM hVar
  simpa using h

end MathlibExtTest.Probability.Finance.PortfolioBeta
