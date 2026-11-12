/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Inference
public import MathlibExt.Probability.Statistics.ConfidenceSet
public import MathlibExt.Probability.Distributions.StudentT
public import Mathlib.Probability.HasLaw

/-!
# One-sample `t` intervals with exact coverage

For an i.i.d. normal sample with `n ≥ 2` and nondegenerate variance, the interval
`xbar ± c * S / sqrt n` covers the mean with probability at least `1 - α` whenever the
`t_{n-1}` central mass on `[-c, c]` reaches `1 - α`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory ProbabilityTheory Real

private theorem one_sample_coverage_aux {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (n - 1)).real (Set.Icc (-c) c) ≥ 1 - α)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    1 - α ≤ P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsqrt_n : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hTmeas : Measurable (fun x : Fin n → ℝ => √(n : ℝ) * ((∑ i, x i) / n - μ) /
      √((∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1))) := by fun_prop
  have hY : MeasurePreserving (fun x : Fin n → ℝ => √(n : ℝ) * ((∑ i, x i) / n - μ) /
      √((∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1)))
      (Measure.pi fun _ : Fin n => gaussianReal μ v) (studentTMeasure (n - 1)) :=
    ⟨hTmeas, map_tStatistic_pi_gaussianReal hn μ hv⟩
  have hT : HasLaw (fun ω : Ω => √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)))
      (studentTMeasure (n - 1)) P :=
    hY.fun_comp_hasLaw hX
  have hEq : P.real {ω | |√(n : ℝ) * ((∑ i, X ω i) / n - μ) /
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1))| ≤ c} =
      (studentTMeasure (n - 1)).real (Set.Icc (-c) c) := by
    rw [hT.measureReal_eq (p := fun t => |t| ≤ c)
      (measurableSet_le (by fun_prop) measurable_const)]
    congr 1
    ext t
    simp [abs_le]
  have hsub : {ω | |√(n : ℝ) * ((∑ i, X ω i) / n - μ) /
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1))| ≤ c} ⊆
        {ω | |(∑ i, X ω i) / n - μ| ≤ c *
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} ∪
        {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases hs : √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0
    · exact Or.inr hs
    · refine Or.inl ?_
      simp only [Set.mem_ofPred_eq]
      have hSpos : 0 < √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hs h.symm)
      rw [abs_div, abs_mul, abs_of_pos hsqrt_n, abs_of_pos hSpos] at hω
      have h1 : √(n : ℝ) * |(∑ i, X ω i) / n - μ| ≤
          c * √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) :=
        (div_le_iff₀ hSpos).mp hω
      have h2 : |(∑ i, X ω i) / n - μ| * √(n : ℝ) ≤
          c * √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) := by
        rw [mul_comm]; exact h1
      exact (le_div_iff₀ hsqrt_n).mpr h2
  have hS0 : P.real
      {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} = 0 := by
    have hsub0 : {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} ⊆
        {ω | √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hω, div_zero]
    have hEq0 : P.real {ω | √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} =
        (studentTMeasure (n - 1)).real {t | t = 0} :=
      hT.measureReal_eq (p := fun t => t = 0) (by
        show MeasurableSet {t : ℝ | t = 0}
        rw [Set.ofPred_eq_eq_singleton]
        exact measurableSet_singleton 0)
    have hnull : (studentTMeasure (n - 1)).real {t : ℝ | t = 0} = 0 := by
      have hs : MeasurableSet {t : ℝ | t = 0} := by
        rw [Set.ofPred_eq_eq_singleton]
        exact measurableSet_singleton 0
      have hvol : volume {t : ℝ | t = 0} = 0 := by
        rw [Set.ofPred_eq_eq_singleton]
        exact Real.volume_singleton
      rw [studentTMeasure, measureReal_def, withDensity_apply _ hs,
        setLIntegral_measure_zero _ _ hvol, ENNReal.toReal_zero]
    have : IsProbabilityMeasure P := hX.isProbabilityMeasure
    have hle0 : P.real
        {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} ≤
        P.real {ω | √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} :=
      measureReal_mono hsub0 (measure_ne_top _ _)
    rw [hEq0, hnull] at hle0
    exact le_antisymm hle0 measureReal_nonneg
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  calc 1 - α ≤ (studentTMeasure (n - 1)).real (Set.Icc (-c) c) := hmass
    _ = P.real {ω | |√(n : ℝ) * ((∑ i, X ω i) / n - μ) /
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1))| ≤ c} := hEq.symm
    _ ≤ P.real ({ω | |(∑ i, X ω i) / n - μ| ≤ c *
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} ∪
        {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} +
        P.real {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} :=
      measureReal_union_le _ _
    _ = P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} := by
      rw [hS0, add_zero]

set_option linter.unusedVariables false in
/-- **One-sample `t` interval with exact coverage**: for an i.i.d. `N(mu, v)` sample with
`n ≥ 2` and `v ≠ 0`, for `c` whose `t_{n-1}` central mass on `[-c, c]` reaches `1 - alpha`,
the interval `xbar ± c * S / sqrt n` covers `mu` with probability at least `1 - alpha`. -/
theorem one_sample_t_interval_coverage {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (n - 1)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    1 - α ≤ P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} := by
  exact one_sample_coverage_aux hn μ hv c hmass hX

end ProbabilityTheory
