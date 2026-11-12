/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import MathlibExt.Probability.Statistics.Nonparametric.KernelDensity

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Pointwise bias of the KDE vanishes at a continuity point of the density.
Domination is by the integrable majorant `B * ‖K ·‖`, so no boundedness or
compact-support hypothesis on the kernel is needed. -/
theorem kde_bias_tends_to_zero {K f : ℝ → ℝ} {t B : ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ B)
    (hK_int : Integrable K) (hK_one : ∫ u, K u = 1)
    (hcont : ContinuousAt f t) :
    Tendsto (fun h : ℝ => ∫ u, K u * f (t - h * u)) (𝓝[>] 0) (𝓝 (f t)) := by
  have hBnn : (0 : ℝ) ≤ B := le_trans (hf_nonneg t) (hf_le t)
  have hshift_meas : ∀ h : ℝ, Measurable (fun u : ℝ => f (t - h * u)) :=
    fun h => hf_meas.comp (measurable_const.sub (measurable_const.mul measurable_id))
  have hfB : ∀ x, ‖f x‖ ≤ B := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
    exact hf_le x
  have hint : ∀ h : ℝ, Integrable (fun u : ℝ => K u * f (t - h * u)) := fun h =>
    hK_int.mul_bdd (hshift_meas h).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => hfB _)
  have hdom : ∀ h : ℝ, ∀ᵐ u ∂(volume : Measure ℝ),
      ‖K u * f (t - h * u)‖ ≤ ‖K u‖ * B := by
    intro h
    filter_upwards with u
    calc ‖K u * f (t - h * u)‖ = ‖K u‖ * ‖f (t - h * u)‖ := norm_mul _ _
      _ ≤ ‖K u‖ * B := mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)
  have hbound_int : Integrable (fun u : ℝ => ‖K u‖ * B) := hK_int.norm.mul_const B
  have hlim : ∀ᵐ u ∂(volume : Measure ℝ),
      Tendsto (fun h : ℝ => K u * f (t - h * u)) (𝓝[>] (0 : ℝ)) (𝓝 (K u * f t)) := by
    apply ae_of_all
    intro u
    have hinner : Tendsto (fun h : ℝ => t - h * u) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
      have hbase : Tendsto (fun h : ℝ => t - h * u) (𝓝 (0 : ℝ)) (𝓝 (t - 0 * u)) :=
        (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).tendsto
      have heq : t - (0 : ℝ) * u = t := by ring
      rw [heq] at hbase
      exact hbase.mono_left nhdsWithin_le_nhds
    have hfc : Tendsto (fun h : ℝ => f (t - h * u)) (𝓝[>] (0 : ℝ)) (𝓝 (f t)) :=
      hcont.tendsto.comp hinner
    exact tendsto_const_nhds.mul hfc
  have hF_meas : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun u : ℝ => K u * f (t - h * u)) volume :=
    Filter.Eventually.of_forall fun h => (hint h).aestronglyMeasurable
  have h_bound : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂(volume : Measure ℝ),
      ‖K u * f (t - h * u)‖ ≤ ‖K u‖ * B :=
    Filter.Eventually.of_forall fun h => hdom h
  have hmain := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℝ))
    (fun u : ℝ => ‖K u‖ * B) hF_meas h_bound hbound_int hlim
  have hfin : (∫ u, K u * f t) = f t := by
    rw [integral_mul_const, hK_one, one_mul]
  rwa [hfin] at hmain

/-- KDE expectation converges to the density value at a continuity point, by
`integral_kde_eq` plus the smoothing limit above. -/
theorem kde_expectation_tendsto {K f : ℝ → ℝ} {t B : ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ B)
    (hK_meas : Measurable K) (hK_int : Integrable K) (hK_one : ∫ u, K u = 1)
    (hcont : ContinuousAt f t)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P) :
    Tendsto (fun h : ℝ => ∫ ω, kde K h (fun i => X i ω) t ∂P) (𝓝[>] 0) (𝓝 (f t)) := by
  have hexp : ∀ h : ℝ, 0 < h → ∫ ω, kde K h (fun i => X i ω) t ∂P
      = ∫ u, K u * f (t - h * u) :=
    fun h hh => integral_kde_eq hn hf_meas hf_nonneg hf_le hX hK_meas hK_int hh t
  refine Tendsto.congr' ?_ (kde_bias_tends_to_zero hf_meas hf_nonneg hf_le
    hK_int hK_one hcont)
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (hexp h (Set.mem_Ioi.mp hh)).symm

end ProbabilityTheory
