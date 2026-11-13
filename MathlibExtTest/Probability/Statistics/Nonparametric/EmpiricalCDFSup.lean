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

-- Positive/use: the coupling fixes atoms (median draw maps to the atom at 0).
example : ProbabilityTheory.cdfQuantile (Measure.dirac (0 : ℝ)) (1 / 2) = 0 := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
  have hset : {x : ℝ | (1 / 2 : ℝ) ≤ cdf (Measure.dirac (0 : ℝ)) x} = Set.Ici 0 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    rw [cdf_eq_real]
    unfold Measure.real
    rw [Measure.dirac_apply]
    by_cases hx : (0 : ℝ) ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx), Pi.one_apply, ENNReal.toReal_one]
      exact iff_of_true (by norm_num) hx
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Iic.mp h)), ENNReal.toReal_zero]
      exact iff_of_false (by norm_num) hx
  unfold ProbabilityTheory.cdfQuantile
  rw [ite_eq_left hmem, hset]
  exact csInf_Ici

-- Boundary: boundary draws map to 0 by definition, which is why hu excludes them
-- (the exact count equality needs hle, available only inside (0,1)).
example : ProbabilityTheory.cdfQuantile (Measure.dirac (0 : ℝ)) 0 = 0 := by
  simp [ProbabilityTheory.cdfQuantile]
