/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the MIT license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Basic.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Two-period difference-in-differences

Main result: under no anticipation and parallel trends, the mean
effect on the treated equals the DiD contrast of observed means.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace MathlibExt.Probability.Causality

/-- Integrability passes to a conditioned law when the cell has mass. -/
private theorem integrable_cond_of_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (_hs : MeasurableSet s) (hpos : μ s ≠ 0)
    {f : Ω → ℝ} (hf : Integrable f μ) : Integrable f μ[|s] := by
  simp only [ProbabilityTheory.cond]
  have hrest : Integrable f (μ.restrict s) := hf.restrict
  have hfin : (μ s)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hpos
  exact hrest.smul_measure hfin

/-- Integrability passes to any conditioned law. -/
private theorem integrable_cond_of_global {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s)
    {f : Ω → ℝ} (hf : Integrable f μ) : Integrable f μ[|s] := by
  by_cases hpos : μ s = 0
  · have hzero : μ[|s] = 0 :=
      ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hpos
    rw [hzero]
    exact integrable_zero_measure
  · exact integrable_cond_of_pos hs hpos hf

/-- The conditioned law is supported on its cell. -/
private theorem ae_mem_cond {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂μ[|s], ω ∈ s :=
  ProbabilityTheory.ae_cond_mem hs

/-- Two-period DiD identification (Section 2.3): the ATT equals the
difference-in-differences of population means. -/
theorem att_eq_diffInDiff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Set Ω} (hT : MeasurableSet T)
    (hTpos : μ T ≠ 0)
    {Y₀ Y₁ : ℕ → Ω → ℝ}
    (hY₀₁ : Integrable (Y₀ 1) μ) (hY₀₂ : Integrable (Y₀ 2) μ)
    (hY₁₂T : Integrable (Y₁ 2) μ[|T])
    (hNoAnt : ∀ ω ∈ T, Y₁ 1 ω = Y₀ 1 ω)
    (hPT : ∫ ω, Y₀ 2 ω - Y₀ 1 ω ∂μ[|T]
      = ∫ ω, Y₀ 2 ω - Y₀ 1 ω ∂μ[|Tᶜ]) :
    ∫ ω, Y₁ 2 ω - Y₀ 2 ω ∂μ[|T] =
      (∫ ω, observed T (Y₀ 2) (Y₁ 2) ω -
        observed T (Y₀ 1) (Y₁ 1) ω ∂μ[|T] -
       ∫ ω, observed T (Y₀ 2) (Y₁ 2) ω -
        observed T (Y₀ 1) (Y₁ 1) ω ∂μ[|Tᶜ]) := by
  have hsTc : MeasurableSet (Tᶜ : Set Ω) := hT.compl
  have hY₀₁T : Integrable (Y₀ 1) μ[|T] :=
    integrable_cond_of_pos hT hTpos hY₀₁
  have hY₀₂T : Integrable (Y₀ 2) μ[|T] :=
    integrable_cond_of_pos hT hTpos hY₀₂
  have hY₀₁Tc : Integrable (Y₀ 1) μ[|Tᶜ] :=
    integrable_cond_of_global hsTc hY₀₁
  have hY₀₂Tc : Integrable (Y₀ 2) μ[|Tᶜ] :=
    integrable_cond_of_global hsTc hY₀₂
  have aeT : ∀ᵐ ω ∂μ[|T], ω ∈ T := ae_mem_cond hT
  have aeTc : ∀ᵐ ω ∂μ[|Tᶜ], ω ∈ Tᶜ := ae_mem_cond hsTc
  have obs2T : ∀ᵐ ω ∂μ[|T],
      observed T (Y₀ 2) (Y₁ 2) ω = Y₁ 2 ω := by
    filter_upwards [aeT] with ω h
    simp [observed, h]
  have obs1T : ∀ᵐ ω ∂μ[|T],
      observed T (Y₀ 1) (Y₁ 1) ω = Y₀ 1 ω := by
    filter_upwards [aeT] with ω h
    have h1 : observed T (Y₀ 1) (Y₁ 1) ω = Y₁ 1 ω := by
      simp [observed, h]
    rw [h1, hNoAnt ω h]
  have obs2Tc : ∀ᵐ ω ∂μ[|Tᶜ],
      observed T (Y₀ 2) (Y₁ 2) ω = Y₀ 2 ω := by
    filter_upwards [aeTc] with ω h
    have hnT : ω ∉ T := h
    simp [observed, hnT]
  have obs1Tc : ∀ᵐ ω ∂μ[|Tᶜ],
      observed T (Y₀ 1) (Y₁ 1) ω = Y₀ 1 ω := by
    filter_upwards [aeTc] with ω h
    have hnT : ω ∉ T := h
    simp [observed, hnT]
  have int_obs_T : ∫ ω, observed T (Y₀ 2) (Y₁ 2) ω -
      observed T (Y₀ 1) (Y₁ 1) ω ∂μ[|T]
      = ∫ ω, Y₁ 2 ω - Y₀ 1 ω ∂μ[|T] := by
    apply integral_congr_ae
    filter_upwards [obs2T, obs1T] with ω h2 h1
    rw [h2, h1]
  have int_obs_Tc : ∫ ω, observed T (Y₀ 2) (Y₁ 2) ω -
      observed T (Y₀ 1) (Y₁ 1) ω ∂μ[|Tᶜ]
      = ∫ ω, Y₀ 2 ω - Y₀ 1 ω ∂μ[|Tᶜ] := by
    apply integral_congr_ae
    filter_upwards [obs2Tc, obs1Tc] with ω h2 h1
    rw [h2, h1]
  have eATT := integral_sub hY₁₂T hY₀₂T
  have eT := integral_sub hY₁₂T hY₀₁T
  have eTc := integral_sub hY₀₂Tc hY₀₁Tc
  have ePT1 := integral_sub hY₀₂T hY₀₁T
  have ePT2 := integral_sub hY₀₂Tc hY₀₁Tc
  have hPT' : ∫ ω, Y₀ 2 ω ∂μ[|T] - ∫ ω, Y₀ 1 ω ∂μ[|T]
      = ∫ ω, Y₀ 2 ω ∂μ[|Tᶜ] - ∫ ω, Y₀ 1 ω ∂μ[|Tᶜ] := by
    rw [← ePT1, ← ePT2]
    exact hPT
  rw [int_obs_T, int_obs_Tc, eATT, eT, eTc]
  linarith

end MathlibExt.Probability.Causality
