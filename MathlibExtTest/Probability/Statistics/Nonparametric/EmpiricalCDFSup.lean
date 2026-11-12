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
  exact iSup_abs_sub_eq_iSup_rat (fun _ => c) (fun _ => d)
    (fun _ => continuousWithinAt_const) (fun _ => continuousWithinAt_const)
    ⟨|c - d|, fun _ => le_rfl⟩

/-- Boundary case: `n = 0` is excluded because the totalized division gives
the zero function, not an empirical CDF. -/
example {Ω : Type*} [MeasurableSpace Ω] (X : Fin 0 → Ω → ℝ) (ω : Ω) (x : ℝ) :
    empCDF (fun i => X i ω) x = 0 := by
  simp [empCDF]

/-- Atomic case: no continuity on `F` is needed; a jump function is allowed. -/
example {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ)
    (eps : ℝ) (hX : ∀ i, Measurable (X i)) :
    MeasurableSet {ω | ∃ q : ℚ, |empCDF (fun i => X i ω) (q : ℝ)
      - (if (q : ℝ) < 0 then (0 : ℝ) else 1)| > eps} := by
  exact measurableSet_uniform_deviation hn X (fun r => if r < 0 then (0 : ℝ) else 1) eps hX
