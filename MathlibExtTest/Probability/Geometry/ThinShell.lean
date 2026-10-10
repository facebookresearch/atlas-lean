/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.ThinShell
public import MathlibExt.Probability.Geometry.UniformInterval

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.ThinShell

example : (0 - Real.sqrt 1) ^ 2 ≤ (0 ^ 2 - 1) ^ 2 / 1 :=
  radius_deviation_sq_le (by norm_num) (by norm_num)

example : (2 - Real.sqrt 1) ^ 2 ≤ (2 ^ 2 - 1) ^ 2 / 1 :=
  radius_deviation_sq_le (by norm_num) (by norm_num)

example : normalizedRadiusVariance
    (0 : Measure (EuclideanSpace ℝ (Fin 1))) = 0 := by
  simp [normalizedRadiusVariance]

example : ¬ IsIsotropicLogConcave
    (0 : Measure (EuclideanSpace ℝ (Fin 1))) := by
  intro h
  have hm := h.1.measure_univ
  simp at hm

example {C : ℝ≥0∞} (h : thinShellVarianceConstant ≤ C) {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    normalizedRadiusVariance μ ≤ C :=
  thinShellVarianceConstant_le_iff.mp h n hn μ hμ

example : IsIsotropicLogConcave (uniformInterval (Real.sqrt 3)) :=
  uniformInterval_sqrt_three_isIsotropicLogConcave

example : normalizedRadiusVariance (uniformInterval (Real.sqrt 3)) ≤
    thinShellVarianceConstant := uniformInterval_variance_le_thinShellConstant

example : (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (1 : ℝ)) ^ 2)
    ∂uniformInterval (Real.sqrt 3)) ≤ thinShellVarianceConstant :=
  uniformInterval_radiusFluctuation_le_thinShellConstant

example : ¬ IsIsotropicLogConcave (uniformInterval 1) :=
  uniformInterval_one_not_isIsotropicLogConcave
