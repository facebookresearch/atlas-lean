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
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import MathlibExt.Probability.Statistics.Nonparametric.KernelDensity

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Pointwise bias of the KDE vanishes at a continuity point of the density. -/
theorem kde_bias_tends_to_zero {K f : ℝ → ℝ} {t B : ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ B)
    (hK_meas : Measurable K) (hK_int : Integrable K) (hK_one : ∫ u, K u = 1)
    (hK_bdd : ∃ C, ∀ u, |K u| ≤ C) (hK_supp : ∃ R, ∀ u, R < |u| → K u = 0)
    (hcont : ContinuousAt f t) :
    Tendsto (fun h : ℝ => ∫ u, K u * f (t - h * u)) (𝓝[>] 0) (𝓝 (f t)) := by
  obtain ⟨R, hR⟩ := hK_supp
  have _hK_meas := hK_meas
  have _hK_bdd := hK_bdd
  set R' : ℝ := max R 0
  have hR'nn : 0 ≤ R' := le_max_right _ _
  have hsupp : ∀ u, R' < |u| → K u = 0 :=
    fun u hu => hR u (lt_of_le_of_lt (le_max_left _ _) hu)
  have hMnn : 0 ≤ ∫ u, ‖K u‖ := integral_nonneg (fun u => norm_nonneg _)
  set M : ℝ := ∫ u, ‖K u‖ with hMdef
  have hshift_meas : ∀ h : ℝ, Measurable (fun u : ℝ => f (t - h * u)) :=
    fun h => hf_meas.comp (measurable_const.sub (measurable_const.mul measurable_id))
  have hfB : ∀ x, ‖f x‖ ≤ B := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
    exact hf_le x
  have hint : ∀ h : ℝ, Integrable (fun u : ℝ => K u * f (t - h * u)) := fun h =>
    hK_int.mul_bdd (hshift_meas h).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => hfB _)
  have hconst_int : Integrable (fun u : ℝ => K u * f t) := hK_int.mul_const (f t)
  have hft_eq : f t = ∫ u, K u * f t := by
    rw [integral_mul_const, hK_one, one_mul]
  have hsub : ∀ h : ℝ, (∫ u, K u * f (t - h * u)) - f t
      = ∫ u, (K u * f (t - h * u) - K u * f t) := by
    intro h
    conv_lhs => rw [hft_eq]
    rw [← integral_sub (hint h) hconst_int]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hM1 : (0:ℝ) < M + 1 := by linarith [hMnn]
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont (ε / (M + 1)) (div_pos hε hM1)
  have hR'1 : (0:ℝ) < R' + 1 := by linarith [hR'nn]
  have hpos : (0:ℝ) < δ / (R' + 1) := div_pos hδpos hR'1
  have hmem : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), 0 < h ∧ h < δ / (R' + 1) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds hpos] with h hlt hmem
    exact ⟨Set.mem_Ioi.mp hmem, hlt⟩
  filter_upwards [hmem] with h hh
  obtain ⟨hhpos, hhlt⟩ := hh
  show dist (∫ u, K u * f (t - h * u)) (f t) < ε
  have hpt : ∀ u : ℝ, ‖K u * f (t - h * u) - K u * f t‖
      ≤ ‖K u‖ * (ε / (M + 1)) := by
    intro u
    by_cases hu : R' < |u|
    · rw [hsupp u hu]
      simp
    · have hu' : |u| ≤ R' := le_of_not_gt hu
      have hclose : dist (t - h * u) t < δ := by
        rw [Real.dist_eq]
        have habs : |t - h * u - t| = h * |u| := by
          have h1 : t - h * u - t = -(h * u) := by ring
          rw [h1, abs_neg, abs_mul, abs_of_pos hhpos]
        rw [habs]
        calc h * |u| ≤ h * R' := mul_le_mul_of_nonneg_left hu' hhpos.le
          _ < δ := by
            have hmul : h * (R' + 1) < δ := (lt_div_iff₀ hR'1).mp hhlt
            have hle : h * R' ≤ h * (R' + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hhpos.le
            exact lt_of_le_of_lt hle hmul
      have hfdlt : dist (f (t - h * u)) (f t) < ε / (M + 1) := hδ hclose
      rw [Real.dist_eq] at hfdlt
      calc ‖K u * f (t - h * u) - K u * f t‖
          = ‖K u‖ * ‖f (t - h * u) - f t‖ := by rw [← mul_sub, norm_mul]
        _ = ‖K u‖ * |f (t - h * u) - f t| := by rw [Real.norm_eq_abs (f (t - h * u) - f t)]
        _ ≤ ‖K u‖ * (ε / (M + 1)) :=
            mul_le_mul_of_nonneg_left (le_of_lt hfdlt) (norm_nonneg _)
  have hdiff_int : Integrable (fun u : ℝ => K u * f (t - h * u) - K u * f t) :=
    (hint h).sub hconst_int
  have hbound_int : Integrable (fun u : ℝ => ‖K u‖ * (ε / (M + 1))) :=
    hK_int.norm.mul_const _
  calc dist (∫ u, K u * f (t - h * u)) (f t)
      = ‖(∫ u, K u * f (t - h * u)) - f t‖ := by rw [Real.dist_eq, Real.norm_eq_abs]
    _ = ‖∫ u, (K u * f (t - h * u) - K u * f t)‖ := by rw [hsub h]
    _ ≤ ∫ u, ‖K u * f (t - h * u) - K u * f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, ‖K u‖ * (ε / (M + 1)) :=
        integral_mono_ae hdiff_int.norm hbound_int (Filter.Eventually.of_forall hpt)
    _ = M * (ε / (M + 1)) := by rw [integral_mul_const, ← hMdef]
    _ < ε := by
        have hring : M * (ε / (M + 1)) = ε * M / (M + 1) := by ring
        rw [hring, div_lt_iff₀ hM1]
        have h2 : ε * (M + 1) = ε * M + ε := by ring
        linarith [hε, h2]

/-- KDE expectation converges to the density value at a continuity point, by
`integral_kde_eq` plus the smoothing limit above. -/
theorem kde_expectation_tendsto {K f : ℝ → ℝ} {t B : ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ B)
    (hK_meas : Measurable K) (hK_int : Integrable K) (hK_one : ∫ u, K u = 1)
    (hK_bdd : ∃ C, ∀ u, |K u| ≤ C) (hK_supp : ∃ R, ∀ u, R < |u| → K u = 0)
    (hcont : ContinuousAt f t)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P) :
    Tendsto (fun h : ℝ => ∫ ω, kde K h (fun i => X i ω) t ∂P) (𝓝[>] 0) (𝓝 (f t)) := by
  have hexp : ∀ h : ℝ, 0 < h → ∫ ω, kde K h (fun i => X i ω) t ∂P
      = ∫ u, K u * f (t - h * u) :=
    fun h hh => integral_kde_eq hn hf_meas hf_nonneg hf_le hX hK_meas hK_int hh t
  refine Tendsto.congr' ?_ (kde_bias_tends_to_zero hf_meas hf_nonneg hf_le hK_meas
    hK_int hK_one hK_bdd hK_supp hcont)
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (hexp h (Set.mem_Ioi.mp hh)).symm

end ProbabilityTheory
