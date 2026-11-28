/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.RegressionDiscontinuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # A sharp regression-discontinuity jump with no treatment effect -/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MathlibExt.Probability.Statistics.RegressionDiscontinuity

open MathlibExt.Probability.Causality

@[expose] public section

/-- **A sharp regression-discontinuity jump with no treatment effect.** Let the running variable
be the identity under the uniform law on `[-1, 1]`, and let both potential outcomes be the
indicator of `[0, ∞)`. Every one-sided interval at zero has positive probability. The potential
outcomes agree for every unit, and the step is a version of their conditional mean given the
running variable. The same step is a version of the observed conditional mean under treatment
at or above zero, with right limit one and left limit zero. This example illustrates the role
of continuity in Imbens and Lemieux (2007), Assumption 2.1; the example is derived here. -/
theorem sharpRD_jump_without_effect :
    let μ := ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1) 1)
    let X : ℝ → ℝ := id
    let m : ℝ → ℝ := (Ici (0 : ℝ)).indicator fun _ => 1
    IsProbabilityMeasure μ ∧
      (∀ ε > 0, μ (X ⁻¹' Ioo 0 ε) ≠ 0 ∧ μ (X ⁻¹' Ioo (-ε) 0) ≠ 0) ∧
      (∀ x, m x - m x = 0) ∧
      (μ[m | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m ∘ X) ∧
      (μ[observed (X ⁻¹' Ici 0) m m | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m ∘ X) ∧
      Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 1) ∧ Tendsto m (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  intro μ X m
  have hvol : volume (Icc (-1 : ℝ) 1) = 2 := by
    rw [Real.volume_Icc]
    norm_num
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite
    (by rw [hvol]; norm_num) (by rw [hvol]; norm_num)
  have hInt : Integrable m μ := (integrable_const (1 : ℝ)).indicator measurableSet_Ici
  have hm : Measurable m := measurable_const.indicator measurableSet_Ici
  have hmver : μ[m | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m ∘ X := by
    change μ[m | MeasurableSpace.comap (id : ℝ → ℝ) inferInstance] =ᵐ[μ] m ∘ id
    simp only [MeasurableSpace.comap_id, Function.comp_id]
    rw [condExp_of_stronglyMeasurable (m := (inferInstance : MeasurableSpace ℝ))
      (m₀ := inferInstance) (μ := μ) le_rfl hm.stronglyMeasurable hInt]
  have hObs := condExp_observed_ae_eq_sharpRDMean (μ := μ) (X := X)
    (show Measurable X from measurable_id) 0 hInt hInt hmver hmver
  have hsame : sharpRDMean 0 m m = m := by
    funext x
    simp [sharpRDMean]
  rw [hsame] at hObs
  have hpositive {s : Set ℝ} (h : volume (Icc (-1 : ℝ) 1 ∩ s) ≠ 0) : μ s ≠ 0 := by
    change ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1) 1) s ≠ 0
    rw [cond_apply measurableSet_Icc, hvol]
    exact mul_ne_zero (by norm_num) h
  refine ⟨inferInstance, ?_, fun _ => sub_self _, hmver, hObs, ?_, ?_⟩
  · intro ε hε
    change μ (Ioo 0 ε) ≠ 0 ∧ μ (Ioo (-ε) 0) ≠ 0
    let δ := min ε 1
    have hδ : 0 < δ := lt_min hε zero_lt_one
    have hδε : δ ≤ ε := min_le_left _ _
    have hδone : δ ≤ 1 := min_le_right _ _
    constructor
    · apply hpositive
      have hsub : Ioo 0 δ ⊆ Icc (-1 : ℝ) 1 ∩ Ioo 0 ε := by
        intro x hx
        exact ⟨⟨by linarith [hx.1], hx.2.le.trans hδone⟩, ⟨hx.1, hx.2.trans_le hδε⟩⟩
      have hvol' : volume (Ioo (0 : ℝ) δ) ≠ 0 := by
        rw [Real.volume_Ioo, sub_zero]
        exact ne_of_gt (ENNReal.ofReal_pos.mpr hδ)
      exact fun hz => hvol' (measure_mono_null hsub hz)
    · apply hpositive
      have hsub : Ioo (-δ) 0 ⊆ Icc (-1 : ℝ) 1 ∩ Ioo (-ε) 0 := by
        intro x hx
        exact ⟨⟨(neg_le_neg hδone).trans hx.1.le, by linarith [hx.2]⟩,
          ⟨lt_of_le_of_lt (neg_le_neg hδε) hx.1, hx.2⟩⟩
      have hvol' : volume (Ioo (-δ) (0 : ℝ)) ≠ 0 := by
        rw [Real.volume_Ioo, zero_sub, neg_neg]
        exact ne_of_gt (ENNReal.ofReal_pos.mpr hδ)
      exact fun hz => hvol' (measure_mono_null hsub hz)
  · have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
      tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx.le) (fun _ : ℝ => (1 : ℝ))).symm
  · have hconst : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] (0 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (indicator_of_notMem (show x ∉ Ici (0 : ℝ) from not_le_of_gt hx)
      (fun _ : ℝ => (1 : ℝ))).symm

end

end MathlibExt.Probability.Statistics.RegressionDiscontinuity
