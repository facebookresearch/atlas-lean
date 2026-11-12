/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TimeSeries.AR1Variance

/-!
# Tests for stationary AR(1) variance

The main theorem and its numeric instance applied with `ρ = 1/2`,
innovation variance `3`, concluding `4`, plus a satisfiability check:
the degenerate instance `X = Y = ε = 0`, `ρ = 0` satisfies the recursion,
stationarity, and independence hypotheses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.TimeSeries.AR1Variance

open MathlibExt.Probability.TimeSeries.AR1Variance

/-- Test: main theorem with `ρ = 1 / 2`, innovation variance `3`, gives `4`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y ε : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hε : MemLp ε 2 μ)
    (hrec : X = fun ω => (1 / 2 : ℝ) * Y ω + ε ω)
    (hstat : variance Y μ = variance X μ)
    (hindep : IndepFun Y ε μ) (hεvar : variance ε μ = 3) :
    variance X μ = 4 := by
  have hρ : ((1 / 2 : ℝ)) ^ 2 ≠ 1 := by norm_num
  have h := stationaryAR1_variance (ρ := (1 / 2 : ℝ)) hρ hX hY hε hrec hstat hindep
  rw [hεvar] at h
  norm_num at h
  exact h

/-- Test: numeric instance theorem applied with exact values. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y ε : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hε : MemLp ε 2 μ)
    (hrec : X = fun ω => (1 / 2 : ℝ) * Y ω + ε ω)
    (hstat : variance Y μ = variance X μ)
    (hindep : IndepFun Y ε μ) (hεvar : variance ε μ = 3) :
    variance X μ = 4 :=
  stationaryAR1_variance_example hX hY hε hrec hstat hindep hεvar

/-- Satisfiability: the degenerate instance `X = Y = ε = 0`, `ρ = 0`
satisfies `hrec`, `hstat`, `hindep`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ((fun _ : Ω => (0 : ℝ))
        = fun ω => (0 : ℝ) * (fun _ : Ω => (0 : ℝ)) ω + (fun _ : Ω => (0 : ℝ)) ω)
      ∧ variance (fun _ : Ω => (0 : ℝ)) μ = variance (fun _ : Ω => (0 : ℝ)) μ
      ∧ IndepFun (fun _ : Ω => (0 : ℝ)) (fun _ : Ω => (0 : ℝ)) μ := by
  refine ⟨?_, rfl, indepFun_const_left 0 _⟩
  funext ω
  simp

end MathlibExtTest.Probability.TimeSeries.AR1Variance
