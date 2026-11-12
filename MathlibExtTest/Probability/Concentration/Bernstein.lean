/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Concentration.Bernstein

open MeasureTheory ProbabilityTheory Finset

/-- Boundary check: the empty family (`n = 0`) with a constant zero
variable family satisfies the Bernstein hypotheses, and the tail set
is empty for `t = 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] :
    P {ω : Ω | (1 : ℝ) ≤ |∑ _i : Fin 0, (0 : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2 / (2 * (0 + 1 * 1 / 3))))) := by
  have hX : iIndepFun (fun (_ : Fin 0) (_ : Ω) => (0 : ℝ)) P :=
    iIndepFun.of_subsingleton
  exact bernstein_inequality (by norm_num) (by norm_num) hX
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (by simp)

/-- Boundary check `t = 0`: the bound is the trivial `2 * exp 0`
shape stated by the theorem. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} (hX : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hbdd : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ 1)
    (hvar : ∑ i, ∫ ω, (X i ω) ^ 2 ∂P ≤ 0) :
    P {ω | (0 : ℝ) ≤ |∑ i, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-((0 : ℝ) ^ 2 / (2 * (0 + 1 * 0 / 3))))) :=
  bernstein_inequality (by norm_num) (by norm_num) hX hXm hmean hbdd hvar

/-- A representative equal to zero except at a null singleton for `dirac 0`. -/
private noncomputable def nullSpike (ω : ℝ) : ℝ :=
  ({1} : Set ℝ).indicator (fun _ => 2) ω

example : (Measure.dirac (0 : ℝ)) {1} = 0 ∧ nullSpike 1 = 2 := by
  norm_num [nullSpike]

example : ¬ ∀ ω, |nullSpike ω| ≤ 1 := by
  intro h
  have := h 1
  norm_num [nullSpike] at this

/-- The a.e. zero representative satisfies Bernstein for any nonnegative
bounds, including `M = 0`, `V = 0`, and positive `M` and `V`. -/
example {M V : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) :
    (Measure.dirac (0 : ℝ)) {ω | (1 : ℝ) ≤ |∑ _i : Fin 1, nullSpike ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2 / (2 * (V + M * 1 / 3))))) := by
  have hX : iIndepFun (fun (_ : Fin 1) => nullSpike) (Measure.dirac 0) :=
    iIndepFun.of_subsingleton
  refine bernstein_inequality hM (by norm_num) hX ?_ ?_ ?_ ?_
  · intro _
    exact measurable_const.indicator (measurableSet_singleton 1)
  · intro _
    simp [nullSpike]
  · intro _
    simpa [nullSpike] using hM
  · simpa [nullSpike] using hV
