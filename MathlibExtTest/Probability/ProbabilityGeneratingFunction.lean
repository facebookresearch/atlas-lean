/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProbabilityGeneratingFunction

open MeasureTheory ProbabilityTheory MathlibExt.Probability

/-! Tests for `MathlibExt.Probability.pgf`. -/

-- Generating function of an independent sum, inside the convergence domain.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ) :
    pgf (fun ω => X ω + Y ω) μ (1 / 2) = pgf X μ (1 / 2) * pgf Y μ (1 / 2) :=
  pgf_add_of_indepFun hX hY hXY (by norm_num [abs_of_pos])

-- Boundary of the convergence domain: `s = -1` is allowed.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℕ} (hX : Measurable X) :
    pgf X μ (-1) = ∑' k, (-1 : ℝ) ^ k * μ.real {ω | X ω = k} :=
  pgf_eq_tsum X μ hX (by norm_num)

-- A probability measure has generating function `1` at `s = 1`.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℕ) : pgf X μ 1 = 1 := by
  simp

-- Concrete computation: a point mass at `3` has generating function `s ^ 3`.
example (s : ℝ) : pgf (fun n : ℕ => n) (Measure.dirac 3) s = s ^ 3 := by
  simp [pgf]

-- At `s = 0` the generating function is `P(X = 0)`.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℕ} (hX : Measurable X) : pgf X μ 0 = μ.real {ω | X ω = 0} :=
  pgf_zero X μ hX

-- Integrability at a negative point inside the convergence domain.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℕ} (hX : Measurable X) : Integrable (fun ω => (-(1 / 3) : ℝ) ^ X ω) μ :=
  integrable_pow_of_abs_le_one hX (by norm_num [abs_of_pos])
