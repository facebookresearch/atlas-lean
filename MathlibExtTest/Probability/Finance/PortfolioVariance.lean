/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.PortfolioVariance
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Finance.PortfolioVariance` -/

open Matrix

namespace MathlibExtTest.PortfolioVariance

example {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {R : ι → Ω → ℝ} (hR : ∀ i, MeasureTheory.MemLp (R i) 2 μ) (i : ι) :
    MathlibExt.Probability.Finance.PortfolioVariance.covMatrix μ R i i =
      ProbabilityTheory.variance (R i) μ := by
  unfold MathlibExt.Probability.Finance.PortfolioVariance.covMatrix
  simp only [Matrix.of_apply]
  exact ProbabilityTheory.covariance_self (hR i).aemeasurable

example {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {R : Fin 2 → Ω → ℝ}
    (hR : ∀ i, MeasureTheory.MemLp (R i) 2 μ) :
    ProbabilityTheory.variance (fun ω => ∑ i, ![1, 2] i * R i ω) μ =
      ![1, 2] ⬝ᵥ
        (MathlibExt.Probability.Finance.PortfolioVariance.covMatrix μ R *ᵥ ![1, 2]) :=
  MathlibExt.Probability.Finance.PortfolioVariance.portfolio_variance_eq_dotProduct_mulVec hR

end MathlibExtTest.PortfolioVariance
