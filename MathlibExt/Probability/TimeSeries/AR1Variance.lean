/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic

/-!
# Stationary AR(1) variance

If `X = ρ * Y + ε` with `Y` independent of `ε`, all square-integrable, and
`Var Y = Var X` (stationarity), then `Var X = Var ε / (1 - ρ²)`. The proof is
`ProbabilityTheory.IndepFun.variance_add` plus `variance_const_mul`, followed
by solving the linear equation `V = ρ² V + σ²`.

Scope: this is the stationary-variance identity under the stated stationarity
and independence hypotheses. Existence of a stationary solution is a
separate gap (ST08.T01, the causal MA(infinity) representation) and is not
proved here. The identity holds whenever `ρ² ≠ 1`, including `Var ε = 0`
(then `Var X = 0`); no positivity hypothesis is needed.

## Main results

- `stationaryAR1_variance`: `Var X = Var ε / (1 - ρ²)`.
- `stationaryAR1_variance_example`: the numeric instance `ρ = 1/2`,
  `Var ε = 3`, giving `Var X = 4`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.TimeSeries.AR1Variance

set_option linter.unusedVariables false in
/-- If `X = ρ * Y + ε` with `Y` independent of `ε`, all square-integrable, and
`Var Y = Var X` (stationarity), then `Var X = Var ε / (1 - ρ²)`. -/
theorem stationaryAR1_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ρ : ℝ} {X Y ε : Ω → ℝ} (hρ : ρ ^ 2 ≠ 1)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hε : MemLp ε 2 μ)
    (hrec : X = fun ω => ρ * Y ω + ε ω) (hstat : variance Y μ = variance X μ)
    (hindep : IndepFun Y ε μ) :
    variance X μ = variance ε μ / (1 - ρ ^ 2) := by
  have hYρ : MemLp (fun ω => ρ * Y ω) 2 μ := hY.const_mul ρ
  have hindep' : IndepFun (fun ω => ρ * Y ω) ε μ :=
    hindep.comp (measurable_const_mul ρ) measurable_id
  have hadd : (fun ω => ρ * Y ω + ε ω) = (fun ω => ρ * Y ω) + ε := rfl
  have hLHS : variance X μ = ρ ^ 2 * variance Y μ + variance ε μ := by
    conv_lhs => rw [hrec, hadd]
    rw [IndepFun.variance_add hYρ hε hindep', variance_const_mul ρ Y μ]
  rw [hstat] at hLHS
  have h1 : (1 : ℝ) - ρ ^ 2 ≠ 0 := fun h => hρ (by linarith)
  have hV : variance X μ * (1 - ρ ^ 2) = variance ε μ := by
    linear_combination hLHS
  rw [eq_div_iff h1]
  exact hV

/-- Numeric instance: `ρ = 1 / 2`, innovation variance `3`, gives stationary
variance `4`. -/
theorem stationaryAR1_variance_example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y ε : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hε : MemLp ε 2 μ)
    (hrec : X = fun ω => (1 / 2 : ℝ) * Y ω + ε ω) (hstat : variance Y μ = variance X μ)
    (hindep : IndepFun Y ε μ) (hεvar : variance ε μ = 3) :
    variance X μ = 4 := by
  have hρ : ((1 / 2 : ℝ)) ^ 2 ≠ 1 := by norm_num
  have h := stationaryAR1_variance hρ hX hY hε hrec hstat hindep
  rw [hεvar] at h
  norm_num at h
  exact h

end MathlibExt.Probability.TimeSeries.AR1Variance
