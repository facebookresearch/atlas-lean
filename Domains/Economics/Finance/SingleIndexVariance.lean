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
# Single-index variance decomposition

Source: Atlas roadmap FI07.T03: an orthogonal single-index residual gives
the systematic plus idiosyncratic variance decomposition. A single-index
return is `R_i ω = α + β * R_M ω + ε ω`, where `ε` is
the residual, orthogonal to the market return in the sense `cov[R_M, ε; μ] = 0`.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.SingleIndexVariance

open MeasureTheory ProbabilityTheory

/-- The single-index return with intercept `α`, market loading `β`, market return
`RM` and residual `ε`: `α + β * RM ω + ε ω`. -/
def singleIndexReturn {Ω : Type*} (α β : ℝ) (RM ε : Ω → ℝ) : Ω → ℝ :=
  fun ω => α + β * RM ω + ε ω

/-- **Systematic plus idiosyncratic variance decomposition (FI07.T03).** For an
orthogonal single-index residual (`cov[RM, ε; μ] = 0`), the variance of the
single-index return splits as `Var[R_i; μ] = β ^ 2 * Var[RM; μ] + Var[ε; μ]`.
The constant `α` drops out, the cross term vanishes by orthogonality, and the
`β ^ 2` factor comes from `variance_const_mul`. The cited Mathlib lemmas
(`variance_add`, `variance_const_mul`, `covariance_const_mul_left`) are not
reproved. -/
theorem singleIndex_variance_decomposition
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (α β : ℝ) (RM ε : Ω → ℝ)
    (hRM : MemLp RM 2 μ) (hε : MemLp ε 2 μ)
    (hCov : cov[RM, ε; μ] = 0) :
    Var[singleIndexReturn α β RM ε; μ] = β ^ 2 * Var[RM; μ] + Var[ε; μ] := by
  have hβRM : MemLp (fun ω => β * RM ω) 2 μ := hRM.const_mul β
  have hX : MemLp (fun ω => α + β * RM ω) 2 μ := (memLp_const α).add hβRM
  have hdecomp : singleIndexReturn α β RM ε = (fun ω => α + β * RM ω) + ε := by
    funext ω
    simp [singleIndexReturn, Pi.add_apply]
  have hInt : Integrable (fun ω => β * RM ω) μ := hβRM.integrable one_le_two
  have hcov0 : cov[fun ω => α + β * RM ω, ε; μ] = 0 := by
    rw [covariance_const_add_left hInt α, covariance_const_mul_left β, hCov, mul_zero]
  have hvarX : Var[fun ω => α + β * RM ω; μ] = β ^ 2 * Var[RM; μ] := by
    rw [variance_const_add hβRM.aestronglyMeasurable α, variance_const_mul]
  rw [hdecomp, variance_add hX hε, hcov0, hvarX, mul_zero, add_zero]

end MathlibExt.Probability.Finance.SingleIndexVariance
