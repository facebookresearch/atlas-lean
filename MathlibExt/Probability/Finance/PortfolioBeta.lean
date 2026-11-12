/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Portfolio beta is linear in portfolio weights

See the contract `/tmp/atlas-econ-50b/lane4/FI07.T01-contract.md` for the source and
clause map. Beta is the covariance of an asset's return with the market return,
divided by the variance of the market return. The portfolio return is the
weight-weighted sum of the asset returns.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.PortfolioBeta

open MeasureTheory ProbabilityTheory

/-- The beta of return `X` against market return `Y` under measure `μ`:
`β = cov[X, Y; μ] / Var[Y; μ]`. -/
noncomputable def assetBeta {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  cov[X, Y; μ] / Var[Y; μ]

set_option linter.unusedVariables false in
/-- **Portfolio beta is linear in portfolio weights (FI07.T01).** When the market
variance is positive, the beta of the portfolio return `∑ i, w i * R i ω` is the
weight-weighted sum of the asset betas. The proof is covariance additivity /
homogeneity in the first slot (`covariance_fun_sum_left`,
`covariance_const_mul_left`) plus `Finset.sum_div`; the cited Mathlib lemmas
are not reproved. The hypothesis `hVar` is contract-required (beta is the
CAPM quantity only when market variance is positive) even though the field
identity holds without it. -/
theorem portfolio_beta_linear
    {ι : Type*} [Fintype ι]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : ι → Ω → ℝ) (RM : Ω → ℝ) (w : ι → ℝ)
    (hR : ∀ i, MemLp (R i) 2 μ) (hM : MemLp RM 2 μ)
    (hVar : 0 < Var[RM; μ]) :
    assetBeta μ (fun ω => ∑ i, w i * R i ω) RM =
      ∑ i, w i * assetBeta μ (R i) RM := by
  have hsum : ∀ i, MemLp (fun ω => w i * R i ω) 2 μ := fun i => (hR i).const_mul (w i)
  unfold assetBeta
  rw [covariance_fun_sum_left hsum hM]
  simp_rw [covariance_const_mul_left]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc]

end MathlibExt.Probability.Finance.PortfolioBeta
