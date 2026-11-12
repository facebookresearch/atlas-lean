/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.EmpiricalCDFSup

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedVariables false in
/-- Positive case: the representation fires for constant functions. -/
example (c d : ℝ) : (⨆ x : ℝ, |c - d|) = ⨆ q : ℚ, |c - d| := by
  exact ProbabilityTheory.iSup_abs_sub_eq_iSup_rat (fun _ => c) (fun _ => d)
    (fun _ => continuousWithinAt_const) (fun _ => continuousWithinAt_const)
    ⟨|c - d|, fun _ => le_rfl⟩

/-- Boundary case: at `n = 0` the uniform-deviation event is still measurable,
by the theorem itself (the empirical CDF is identically zero there). -/
example {Ω : Type*} [MeasurableSpace Ω] (X : Fin 0 → Ω → ℝ)
    (F : ℝ → ℝ) (eps : ℝ)
    (hX : ∀ i, Measurable (X i)) :
    MeasurableSet {ω | ∃ q : ℚ, |ProbabilityTheory.empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)| > eps} :=
  ProbabilityTheory.measurableSet_uniform_deviation X F eps hX

/-- Atomic case: no continuity on `F` is needed; a jump function is allowed. -/
example {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ)
    (eps : ℝ) (hX : ∀ i, Measurable (X i)) :
    MeasurableSet {ω | ∃ q : ℚ, |ProbabilityTheory.empCDF (fun i => X i ω) (q : ℝ)
      - (if (q : ℝ) < 0 then (0 : ℝ) else 1)| > eps} := by
  exact ProbabilityTheory.measurableSet_uniform_deviation X (fun r => if r < 0 then (0 : ℝ) else 1) eps hX
