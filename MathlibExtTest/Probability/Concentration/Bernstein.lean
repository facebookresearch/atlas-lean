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
  have hempty : {ω : Ω | (1 : ℝ) ≤ |∑ _i : Fin 0, (0 : ℝ)|} = ∅ := by
    ext ω
    simp
  rw [hempty]
  simp

/-- Boundary check `t = 0`: the bound is the trivial `2 * exp 0`
shape stated by the theorem. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} (hX : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hbdd : ∀ i ω, |X i ω| ≤ 1)
    (hvar : ∑ i, ∫ ω, (X i ω) ^ 2 ∂P ≤ 0) :
    P {ω | (0 : ℝ) ≤ |∑ i, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-((0 : ℝ) ^ 2 / (2 * (0 + 1 * 0 / 3))))) :=
  bernstein_inequality (by norm_num) (by norm_num) hX hXm hmean hbdd hvar
