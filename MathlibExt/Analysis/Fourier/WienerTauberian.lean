/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import MathlibExt.Analysis.Fourier.Scaling

open MeasureTheory
open scoped Convolution FourierTransform

namespace MathlibExt.Analysis.Fourier.WienerWanted

/-! ## Private helpers for Wiener's L¹ Tauberian theorem (all `wtaub`-prefixed). -/

-- Fourier linearity on plain functions.
private theorem wtaub_char_int {u : ℝ → ℂ} (hu : Integrable u volume) (ξ : ℝ) :
    Integrable (fun x => Real.fourierChar (-(x * ξ)) • u x) volume := by
  have c : Continuous fun x : ℝ => Real.fourierChar (-(x * ξ)) :=
    Real.continuous_fourierChar.comp ((continuous_id.mul continuous_const).neg)
  have m : AEStronglyMeasurable
      (fun x => Real.fourierChar (-(x * ξ)) • u x) volume :=
    c.aestronglyMeasurable.smul hu.aestronglyMeasurable
  rw [← integrable_norm_iff m]
  simpa using hu.norm

private theorem wtaub_fourier_sub {u v : ℝ → ℂ} (hu : Integrable u volume)
    (hv : Integrable v volume) (ξ : ℝ) :
    𝓕 (fun x => u x - v x) ξ = 𝓕 u ξ - 𝓕 v ξ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq,
    ← integral_sub (wtaub_char_int hu ξ) (wtaub_char_int hv ξ)]
  congr 1
  ext x
  exact smul_sub _ _ _

private theorem wtaub_fourier_add {u v : ℝ → ℂ} (hu : Integrable u volume)
    (hv : Integrable v volume) (ξ : ℝ) :
    𝓕 (fun x => u x + v x) ξ = 𝓕 u ξ + 𝓕 v ξ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq,
    ← integral_add (wtaub_char_int hu ξ) (wtaub_char_int hv ξ)]
  congr 1
  ext x
  exact smul_add _ _ _

private theorem wtaub_fourier_const_mul (a : ℂ) (u : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => a * u x) ξ = a * 𝓕 u ξ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
  congr 1
  ext x
  simp only [Circle.smul_def, smul_eq_mul]
  ring

-- L¹ continuity of translation.
private theorem wtaub_translate_tendsto_cs {u' : ℝ → ℂ}
    (hcont : Continuous u') (hs : HasCompactSupport u') :
    Filter.Tendsto (fun τ : ℝ => ∫ x, ‖u' (x - τ) - u' x‖) (nhds 0) (nhds 0) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport u' ⊆ Metric.closedBall 0 R := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
      hs.isCompact.isBounded
    exact ⟨|C| + 1, hC.trans (fun x hx => Metric.mem_closedBall.mpr
      ((Metric.mem_closedBall.mp hx).trans
        ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))))⟩
  obtain ⟨M, hMpos, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, ‖u' y‖ ≤ M := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
      (hs.isCompact.image hcont).isBounded
    refine ⟨|C| + 1, by positivity, fun y => ?_⟩
    by_cases hy : y ∈ tsupport u'
    · have h1 : dist (u' y) 0 ≤ C :=
        Metric.mem_closedBall.mp (hC ⟨y, hy, rfl⟩)
      calc ‖u' y‖ = dist (u' y) 0 := (dist_zero_right _).symm
        _ ≤ |C| + 1 :=
          h1.trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      positivity
  have hBint : Integrable
      (Set.indicator (Metric.closedBall 0 (R + 1)) (fun _ : ℝ => 2 * M))
      volume := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
    exact MeasureTheory.integrableOn_const
      ((isCompact_closedBall 0 _).measure_lt_top.ne)
  have hmeas : ∀ᶠ τ : ℝ in nhds 0, AEStronglyMeasurable
      (fun x => ‖u' (x - τ) - u' x‖) volume := by
    filter_upwards with τ
    exact ((hcont.comp (continuous_id.sub continuous_const)).sub
      hcont).norm.aestronglyMeasurable
  have hlim : ∀ᵐ x : ℝ ∂volume, Filter.Tendsto (fun τ => ‖u' (x - τ) - u' x‖)
      (nhds 0) (nhds 0) := by
    filter_upwards with x
    have h2 : Filter.Tendsto (fun τ : ℝ => x - τ) (nhds 0) (nhds (x - 0)) :=
      tendsto_const_nhds.sub Filter.tendsto_id
    rw [sub_zero] at h2
    have h3 : Filter.Tendsto (fun τ : ℝ => u' (x - τ) - u' x) (nhds 0)
        (nhds (u' x - u' x)) := ((hcont.tendsto _).comp h2).sub tendsto_const_nhds
    rw [sub_self] at h3
    simpa using h3.norm
  have hbound : ∀ᶠ τ : ℝ in nhds 0, ∀ᵐ x : ℝ ∂volume,
      ‖‖u' (x - τ) - u' x‖‖ ≤
        Set.indicator (Metric.closedBall 0 (R + 1)) (fun _ : ℝ => 2 * M) x := by
    have h1 : ∀ᶠ τ : ℝ in nhds 0, τ ∈ Metric.closedBall 0 1 := by
      filter_upwards [Metric.ball_mem_nhds 0 one_pos] with τ hτ
      exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hτ))
    filter_upwards [h1] with τ hτ
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    by_cases hx : x ∈ Metric.closedBall 0 (R + 1)
    · rw [Set.indicator_of_mem hx]
      calc ‖u' (x - τ) - u' x‖ ≤ ‖u' (x - τ)‖ + ‖u' x‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    · rw [Set.indicator_of_notMem hx]
      have hτ1 : ‖τ‖ ≤ 1 := by
        have hle : dist τ 0 ≤ 1 := Metric.mem_closedBall.mp hτ
        rwa [dist_zero_right] at hle
      have hxR1 : R + 1 < ‖x‖ := by
        have hne : ¬ ‖x‖ ≤ R + 1 := by
          have hle : dist x 0 ≤ R + 1 → False := fun h => hx
            (Metric.mem_closedBall.mpr h)
          rwa [dist_zero_right] at hle
        exact lt_of_not_ge hne
      have hdiff : R < ‖x - τ‖ := by
        have h := norm_sub_norm_le x τ
        linarith
      have hxτ : x - τ ∉ tsupport u' := by
        intro hmem
        have hle : ‖x - τ‖ ≤ R := by
          have hmem' : x - τ ∈ Metric.closedBall 0 R := hR hmem
          have hle' : dist (x - τ) 0 ≤ R := Metric.mem_closedBall.mp hmem'
          rwa [dist_zero_right] at hle'
        exact (not_le_of_gt hdiff) hle
      have hx2 : x ∉ tsupport u' := by
        intro hmem
        apply hx
        have hle : dist x 0 ≤ R := Metric.mem_closedBall.mp (hR hmem)
        exact Metric.mem_closedBall.mpr
          (hle.trans (le_add_of_nonneg_right zero_le_one))
      have e1 : u' (x - τ) = 0 := image_eq_zero_of_notMem_tsupport hxτ
      have e2 : u' x = 0 := image_eq_zero_of_notMem_tsupport hx2
      simp [e1, e2]
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (Set.indicator (Metric.closedBall 0 (R + 1)) (fun _ : ℝ => 2 * M))
    hmeas hbound hBint hlim
  simpa using hDCT

private theorem wtaub_translate_tendsto {u : ℝ → ℂ} (hu : Integrable u volume) :
    Filter.Tendsto (fun τ : ℝ => ∫ x, ‖u (x - τ) - u x‖) (nhds 0) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨u', hs, hint, hcont, huint⟩ :=
    hu.exists_hasCompactSupport_integral_sub_le (show (0 : ℝ) < ε / 3 by linarith)
  have key := wtaub_translate_tendsto_cs hcont hs
  rw [Metric.tendsto_nhds] at key
  have hev := key (ε / 3) (by linarith)
  filter_upwards [hev] with τ hτ
  have hτ' : ∫ x, ‖u' (x - τ) - u' x‖ < ε / 3 := by
    have hnn : 0 ≤ ∫ x, ‖u' (x - τ) - u' x‖ :=
      integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
    rw [dist_zero_right, Real.norm_of_nonneg hnn] at hτ
    exact hτ
  have hpt : ∀ x : ℝ, ‖u (x - τ) - u x‖ ≤
      (‖u (x - τ) - u' (x - τ)‖ + ‖u' (x - τ) - u' x‖) + ‖u' x - u x‖ := by
    intro x
    have e : u (x - τ) - u x =
        (u (x - τ) - u' (x - τ) + (u' (x - τ) - u' x)) + (u' x - u x) := by
      abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have i0 : Integrable (fun x => ‖u (x - τ) - u x‖) volume :=
    ((hu.comp_sub_right τ).sub hu).norm
  have i1 : Integrable (fun x => ‖u (x - τ) - u' (x - τ)‖) volume :=
    ((hu.sub huint).norm).comp_sub_right τ
  have i2 : Integrable (fun x => ‖u' (x - τ) - u' x‖) volume :=
    ((huint.comp_sub_right τ).sub huint).norm
  have i3 : Integrable (fun x => ‖u' x - u x‖) volume := (huint.sub hu).norm
  have e1 : (∫ x, ‖u (x - τ) - u' (x - τ)‖) = ∫ x, ‖u x - u' x‖ := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun y => ‖u y - u' y‖) τ
    simpa using h
  have e3 : (∫ x, ‖u' x - u x‖) = ∫ x, ‖u x - u' x‖ := by
    congr 1
    ext x
    exact norm_sub_rev _ _
  have i12 : Integrable
      (fun x => (‖u (x - τ) - u' (x - τ)‖ + ‖u' (x - τ) - u' x‖)) volume :=
    i1.add i2
  have i123 : Integrable
      (fun x => ((‖u (x - τ) - u' (x - τ)‖ + ‖u' (x - τ) - u' x‖) +
        ‖u' x - u x‖)) volume := i12.add i3
  have hmono : (∫ x, ‖u (x - τ) - u x‖) ≤
      ∫ x, ((‖u (x - τ) - u' (x - τ)‖ + ‖u' (x - τ) - u' x‖) +
        ‖u' x - u x‖) := integral_mono i0 i123 hpt
  have s1 : (∫ x, ((‖u (x - τ) - u' (x - τ)‖ + ‖u' (x - τ) - u' x‖) +
      ‖u' x - u x‖)) = (∫ x, (‖u (x - τ) - u' (x - τ)‖ + ‖u' (x - τ) - u' x‖)) +
      (∫ x, ‖u' x - u x‖) := integral_add i12 i3
  have s2 : (∫ x, (‖u (x - τ) - u' (x - τ)‖ + ‖u' (x - τ) - u' x‖)) =
      (∫ x, ‖u (x - τ) - u' (x - τ)‖) + (∫ x, ‖u' (x - τ) - u' x‖) :=
    integral_add i1 i2
  rw [s1, s2, e1, e3] at hmono
  have htri : ∫ x, ‖u (x - τ) - u x‖ ≤
      2 * (ε / 3) + ∫ x, ‖u' (x - τ) - u' x‖ :=
    hmono.trans (by linarith [hint, hτ'])
  have hnn : 0 ≤ ∫ x, ‖u (x - τ) - u x‖ :=
    integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
  rw [dist_zero_right, Real.norm_of_nonneg hnn]
  linarith

private theorem wtaub_translate_sub_eq {u : ℝ → ℂ} (τ τ₀ : ℝ) :
    (∫ x, ‖u (x - τ) - u (x - τ₀)‖) = ∫ y, ‖u (y - (τ - τ₀)) - u y‖ := by
  have e : ∀ x : ℝ, x - τ₀ - (τ - τ₀) = x - τ := fun x => by ring
  have h := integral_sub_right_eq_self (μ := volume)
    (fun y => ‖u (y - (τ - τ₀)) - u y‖) τ₀
  rw [← h]
  congr 1
  ext x
  change ‖u (x - τ) - u (x - τ₀)‖ = ‖u (x - τ₀ - (τ - τ₀)) - u (x - τ₀)‖
  rw [e x]

private theorem wtaub_translate_continuous {u : ℝ → ℂ} (hu : Integrable u volume) :
    Continuous (fun τ : ℝ => ∫ x, ‖u (x - τ) - u x‖) := by
  have hbound : ∀ τ τ₀ : ℝ,
      |(∫ x, ‖u (x - τ) - u x‖) - (∫ x, ‖u (x - τ₀) - u x‖)| ≤
      ∫ x, ‖u (x - (τ - τ₀)) - u x‖ := by
    intro τ τ₀
    have hF : Integrable (fun x => ‖u (x - τ) - u x‖) volume :=
      ((hu.comp_sub_right τ).sub hu).norm
    have hG : Integrable (fun x => ‖u (x - τ₀) - u x‖) volume :=
      ((hu.comp_sub_right τ₀).sub hu).norm
    have hpt : ∀ x : ℝ, |‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖| ≤
        ‖u (x - τ) - u (x - τ₀)‖ := by
      intro x
      have e : (u (x - τ) - u x) - (u (x - τ₀) - u x)
          = u (x - τ) - u (x - τ₀) := by abel
      calc |‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖|
            ≤ ‖(u (x - τ) - u x) - (u (x - τ₀) - u x)‖ :=
              abs_norm_sub_norm_le _ _
          _ = ‖u (x - τ) - u (x - τ₀)‖ := by rw [e]
    have hFG : Integrable
        (fun x => ‖‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖‖) volume :=
      (hF.sub hG).norm
    have hRHS : Integrable (fun x => ‖u (x - τ) - u (x - τ₀)‖) volume :=
      ((hu.comp_sub_right τ).sub (hu.comp_sub_right τ₀)).norm
    have hpt2 : ∀ x : ℝ, ‖‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖‖ ≤
        ‖u (x - τ) - u (x - τ₀)‖ := by
      intro x
      rw [Real.norm_eq_abs]
      exact hpt x
    have hmono : |(∫ x, ‖u (x - τ) - u x‖) - (∫ x, ‖u (x - τ₀) - u x‖)| ≤
        ∫ x, ‖u (x - τ) - u (x - τ₀)‖ := by
      have hsub : (∫ x, ‖u (x - τ) - u x‖) - (∫ x, ‖u (x - τ₀) - u x‖) =
          ∫ x, (‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖) := by
        have h := integral_sub hF hG
        have hstated : (∫ x, (‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖)) =
            (∫ x, ‖u (x - τ) - u x‖) - (∫ x, ‖u (x - τ₀) - u x‖) := h
        exact hstated.symm
      rw [hsub]
      have h2 : |∫ x, (‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖)| ≤
          ∫ x, ‖‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖‖ := by
        have h := norm_integral_le_integral_norm (μ := volume)
          (fun x => (‖u (x - τ) - u x‖ - ‖u (x - τ₀) - u x‖) : ℝ → ℝ)
        rw [Real.norm_eq_abs] at h
        exact h
      exact h2.trans (integral_mono hFG hRHS hpt2)
    exact hmono.trans_eq (wtaub_translate_sub_eq τ τ₀)
  rw [continuous_iff_continuousAt]
  intro τ₀
  have hsub : Filter.Tendsto (fun τ : ℝ => τ - τ₀) (nhds τ₀) (nhds 0) := by
    have h1 : Filter.Tendsto (fun τ : ℝ => τ) (nhds τ₀) (nhds τ₀) :=
      Filter.tendsto_id
    have h2 : Filter.Tendsto (fun _ : ℝ => τ₀) (nhds τ₀) (nhds τ₀) :=
      tendsto_const_nhds
    have h := h1.sub h2
    simpa using h
  have h0 : Filter.Tendsto (fun τ : ℝ => ∫ x, ‖u (x - (τ - τ₀)) - u x‖)
      (nhds τ₀) (nhds 0) := (wtaub_translate_tendsto hu).comp hsub
  change Filter.Tendsto (fun τ : ℝ => ∫ x, ‖u (x - τ) - u x‖) (nhds τ₀)
    (nhds (∫ x, ‖u (x - τ₀) - u x‖))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp h0) ε hε
  filter_upwards [hev] with τ hτ
  have hnn : 0 ≤ ∫ x, ‖u (x - (τ - τ₀)) - u x‖ :=
    integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
  have hd : ∫ x, ‖u (x - (τ - τ₀)) - u x‖ < ε := by
    have hτ2 := hτ
    rw [dist_zero_right, Real.norm_of_nonneg hnn] at hτ2
    exact hτ2
  rw [Real.dist_eq]
  exact (hbound τ τ₀).trans_lt hd

private theorem wtaub_translate_bound {u : ℝ → ℂ} (hu : Integrable u volume)
    (τ : ℝ) : 0 ≤ ∫ x, ‖u (x - τ) - u x‖ ∧
    ∫ x, ‖u (x - τ) - u x‖ ≤ 2 * ∫ x, ‖u x‖ := by
  have i0 : Integrable (fun x => ‖u (x - τ) - u x‖) volume :=
    ((hu.comp_sub_right τ).sub hu).norm
  have i1 : Integrable (fun x => ‖u (x - τ)‖) volume := hu.norm.comp_sub_right τ
  have e1 : (∫ x, ‖u (x - τ)‖) = ∫ x, ‖u x‖ := by
    have h := integral_sub_right_eq_self (μ := volume) (fun y => ‖u y‖) τ
    simpa using h
  constructor
  · exact integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
  · calc ∫ x, ‖u (x - τ) - u x‖
          ≤ ∫ x, (‖u (x - τ)‖ + ‖u x‖) :=
            integral_mono i0 (i1.add hu.norm) (fun x => norm_sub_le _ _)
      _ = (∫ x, ‖u (x - τ)‖) + ∫ x, ‖u x‖ := integral_add i1 hu.norm
      _ = 2 * ∫ x, ‖u x‖ := by rw [e1]; ring

-- Dominated dilation limit.
private theorem wtaub_dilation_limit {k u : ℝ → ℂ} (hk : Integrable k volume)
    (hu : Integrable u volume) :
    Filter.Tendsto (fun δ : ℝ => ∫ y, ‖k y‖ * ∫ x, ‖u (x - δ * y) - u x‖)
      (nhds 0) (nhds 0) := by
  have hω := wtaub_translate_continuous hu
  have hB : Integrable (fun y => ‖k y‖ * (2 * ∫ x, ‖u x‖)) volume :=
    hk.norm.mul_const _
  have hmeas : ∀ᶠ δ : ℝ in nhds 0, AEStronglyMeasurable
      (fun y => ‖k y‖ * ∫ x, ‖u (x - δ * y) - u x‖) volume := by
    filter_upwards with δ
    exact hk.norm.aestronglyMeasurable.mul
      (hω.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℝ in nhds 0, ∀ᵐ y : ℝ ∂volume,
      ‖‖k y‖ * ∫ x, ‖u (x - δ * y) - u x‖‖ ≤ ‖k y‖ * (2 * ∫ x, ‖u x‖) := by
    filter_upwards with δ
    filter_upwards with y
    have hnn : 0 ≤ ‖k y‖ * ∫ x, ‖u (x - δ * y) - u x‖ :=
      mul_nonneg (norm_nonneg _)
        (integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (wtaub_translate_bound hu (δ * y)).2
      (norm_nonneg _)
  have hlim : ∀ᵐ y : ℝ ∂volume, Filter.Tendsto
      (fun δ => ‖k y‖ * ∫ x, ‖u (x - δ * y) - u x‖) (nhds 0) (nhds 0) := by
    filter_upwards with y
    have h1a : Filter.Tendsto (fun δ : ℝ => δ) (nhds 0) (nhds (0 : ℝ)) :=
      Filter.tendsto_id
    have h1 : Filter.Tendsto (fun δ : ℝ => δ * y) (nhds 0) (nhds 0) := by
      simpa using h1a.mul tendsto_const_nhds
    have h2 : Filter.Tendsto (fun δ : ℝ => ∫ x, ‖u (x - δ * y) - u x‖)
        (nhds 0) (nhds 0) := (wtaub_translate_tendsto hu).comp h1
    have h3 : Filter.Tendsto (fun δ : ℝ => ‖k y‖ * ∫ x, ‖u (x - δ * y) - u x‖)
        (nhds 0) (nhds 0) := by
      have h := Filter.Tendsto.const_mul (‖k y‖) h2
      simpa using h
    exact h3
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (fun y => ‖k y‖ * (2 * ∫ x, ‖u x‖)) hmeas hbound hB hlim
  simpa using hDCT

-- Young's inequality in L¹.
private theorem wtaub_conv_integrable {u w : ℝ → ℂ} (hu : Integrable u volume)
    (hw : Integrable w volume) :
    Integrable (u ⋆[ContinuousLinearMap.mul ℂ ℂ] w) volume :=
  hu.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hw

private theorem wtaub_conv_norm_le {u w : ℝ → ℂ} (hu : Integrable u volume)
    (hw : Integrable w volume) :
    ∫ x, ‖(u ⋆[ContinuousLinearMap.mul ℂ ℂ] w) x‖ ≤
      (∫ x, ‖u x‖) * (∫ x, ‖w x‖) := by
  have hpt : ∀ x : ℝ, ‖(u ⋆[ContinuousLinearMap.mul ℂ ℂ] w) x‖ ≤
      ((fun a => ‖u a‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun a => ‖w a‖)) x := by
    intro x
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    ext t
    rw [ContinuousLinearMap.mul_apply', ContinuousLinearMap.mul_apply', norm_mul]
  calc ∫ x, ‖(u ⋆[ContinuousLinearMap.mul ℂ ℂ] w) x‖
        ≤ ∫ x, ((fun a => ‖u a‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
            (fun a => ‖w a‖)) x :=
          integral_mono (wtaub_conv_integrable hu hw).norm
            (hu.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hw.norm)
            hpt
      _ = (∫ x, ‖u x‖) * (∫ x, ‖w x‖) := by
          rw [MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
            hu.norm hw.norm, ContinuousLinearMap.mul_apply']

-- Smooth kernel with compactly supported Fourier transform.
private theorem wtaub_bump :
    ∃ V : ℝ → ℂ, Continuous V ∧ Integrable V volume ∧
      (∀ ξ : ℝ, ‖𝓕 V ξ‖ ≤ 1) ∧ (∀ ξ : ℝ, |ξ| ≤ 1 → 𝓕 V ξ = 1) ∧
      (∀ ξ : ℝ, 2 ≤ |ξ| → 𝓕 V ξ = 0) ∧ ∫ x, V x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  have hbRIn : b.rIn = 1 := rfl
  have hbROut : b.rOut = 2 := rfl
  have hφdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Complex.ofRealCLM ∘ ⇑b) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hφsupp : HasCompactSupport (⇑Complex.ofRealCLM ∘ ⇑b) :=
    b.hasCompactSupport.comp_left (by simp)
  have hΦeq : ∀ x : ℝ,
      ((hφsupp.toSchwartzMap hφdiff : SchwartzMap ℝ ℂ) : ℝ → ℂ) x =
        Complex.ofRealCLM (b x) := fun x =>
    HasCompactSupport.toSchwartzMap_toFun hφsupp hφdiff x
  have hVfourier : ∀ ξ : ℝ,
      𝓕 (⇑(FourierTransformInv.fourierInv
        (hφsupp.toSchwartzMap hφdiff))) ξ =
        Complex.ofRealCLM (b ξ) := by
    intro ξ
    have hpair := FourierInvPair.fourier_fourierInv_eq
      (E := SchwartzMap ℝ ℂ) (F := SchwartzMap ℝ ℂ)
      (hφsupp.toSchwartzMap hφdiff)
    calc 𝓕 (⇑(FourierTransformInv.fourierInv
            (hφsupp.toSchwartzMap hφdiff))) ξ
          = ⇑(FourierTransform.fourier (FourierTransformInv.fourierInv
            (hφsupp.toSchwartzMap hφdiff))) ξ := by
            rw [SchwartzMap.fourier_coe]
        _ = ⇑(hφsupp.toSchwartzMap hφdiff) ξ := by rw [hpair]
        _ = Complex.ofRealCLM (b ξ) := hΦeq ξ
  refine ⟨⇑(FourierTransformInv.fourierInv (hφsupp.toSchwartzMap hφdiff)),
    (FourierTransformInv.fourierInv
      (hφsupp.toSchwartzMap hφdiff)).continuous,
    (FourierTransformInv.fourierInv
      (hφsupp.toSchwartzMap hφdiff)).integrable, ?_, ?_, ?_, ?_⟩
  · intro ξ
    rw [hVfourier ξ]
    calc ‖Complex.ofRealCLM (b ξ)‖ = ‖b ξ‖ := Complex.ofRealLI.norm_map _
        _ = |b ξ| := Real.norm_eq_abs _
        _ ≤ 1 := by rw [abs_of_nonneg b.nonneg]; exact b.le_one
  · intro ξ hξ
    rw [hVfourier ξ, Complex.ofRealCLM_apply]
    have hmem : ξ ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      rw [hbRIn]
      apply Metric.mem_closedBall.mpr
      rw [dist_zero_right, Real.norm_eq_abs]
      exact hξ
    have hb1 : b ξ = 1 := b.one_of_mem_closedBall hmem
    rw [hb1]
    exact Complex.ofReal_one
  · intro ξ hξ
    rw [hVfourier ξ, Complex.ofRealCLM_apply]
    have hdist : (2 : ℝ) ≤ dist ξ 0 := by
      rw [dist_zero_right, Real.norm_eq_abs]
      exact hξ
    have hb0 : b ξ = 0 :=
      b.zero_of_le_dist (by rw [hbROut]; exact hdist)
    rw [hb0]
    exact Complex.ofReal_zero
  · have e : ∀ v : ℝ, Real.fourierChar (-(v * 0)) •
        (⇑(FourierTransformInv.fourierInv
          (hφsupp.toSchwartzMap hφdiff)) : ℝ → ℂ) v =
        ⇑(FourierTransformInv.fourierInv
          (hφsupp.toSchwartzMap hφdiff)) v := by
      intro v
      rw [mul_zero, neg_zero, Real.fourierChar.map_zero_eq_one, one_smul]
    have hFV0 : 𝓕 (⇑(FourierTransformInv.fourierInv
        (hφsupp.toSchwartzMap hφdiff))) 0 =
        ∫ x, ⇑(FourierTransformInv.fourierInv
          (hφsupp.toSchwartzMap hφdiff)) x := by
      rw [Real.fourier_real_eq]
      congr 1
      ext v
      exact e v
    have hmem0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      rw [hbRIn]
      exact Metric.mem_closedBall.mpr (by simp)
    have hb10 : b (0 : ℝ) = 1 := b.one_of_mem_closedBall hmem0
    calc ∫ x, ⇑(FourierTransformInv.fourierInv
            (hφsupp.toSchwartzMap hφdiff)) x
          = 𝓕 (⇑(FourierTransformInv.fourierInv
            (hφsupp.toSchwartzMap hφdiff))) 0 := hFV0.symm
        _ = Complex.ofRealCLM (b 0) := hVfourier 0
        _ = 1 := by rw [hb10, Complex.ofRealCLM_apply]; exact Complex.ofReal_one

-- Modulated dilations.
private noncomputable def wtaubModDil (V : ℝ → ℂ) (w₀ δ : ℝ) : ℝ → ℂ :=
  fun x => ((Real.fourierChar (w₀ * x) : Circle) : ℂ) * ((δ : ℂ) * V (δ * x))

private noncomputable def wtaubDil (W : ℝ → ℂ) (lam : ℝ) : ℝ → ℂ :=
  fun x => (lam : ℂ) * W (lam * x)

private theorem wtaub_modDil_integrable {V : ℝ → ℂ} (hV : Integrable V volume)
    (w₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) : Integrable (wtaubModDil V w₀ δ) volume := by
  have hVδ : Integrable (fun x : ℝ => V (δ * x)) volume :=
    hV.comp_mul_left' (ne_of_gt hδ)
  have hD : Integrable (fun x : ℝ => (δ : ℂ) * V (δ * x)) volume :=
    hVδ.const_mul _
  have hc : Continuous fun x : ℝ => Real.fourierChar (w₀ * x) :=
    Real.continuous_fourierChar.comp (continuous_const.mul continuous_id)
  have hmeas : AEStronglyMeasurable (wtaubModDil V w₀ δ) volume := by
    have e : wtaubModDil V w₀ δ =
        fun x => Real.fourierChar (w₀ * x) • ((δ : ℂ) * V (δ * x)) := by
      ext x
      change ((Real.fourierChar (w₀ * x) : Circle) : ℂ) * _ = _
      rw [Circle.smul_def, smul_eq_mul]
    rw [e]
    exact hc.aestronglyMeasurable.smul hD.aestronglyMeasurable
  rw [← integrable_norm_iff hmeas]
  have enorm : (fun x => ‖wtaubModDil V w₀ δ x‖) =
      fun x : ℝ => ‖(δ : ℂ) * V (δ * x)‖ := by
    ext x
    change ‖((Real.fourierChar (w₀ * x) : Circle) : ℂ) * _‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul]
  rw [enorm]
  have e2 : (fun x : ℝ => ‖(δ : ℂ) * V (δ * x)‖) =
      fun x : ℝ => δ * ‖V (δ * x)‖ := by
    ext x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
  rw [e2]
  exact (hV.norm.comp_mul_left' (ne_of_gt hδ)).const_mul _

private theorem wtaub_modDil_norm {V : ℝ → ℂ} (_hV : Integrable V volume)
    (w₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, ‖wtaubModDil V w₀ δ x‖ = ∫ x, ‖V x‖ := by
  have enorm : (fun x => ‖wtaubModDil V w₀ δ x‖) =
      fun x : ℝ => δ * ‖V (δ * x)‖ := by
    ext x
    change ‖((Real.fourierChar (w₀ * x) : Circle) : ℂ) * _‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hδ.le]
  have hsub : (∫ x : ℝ, ‖V (δ * x)‖) = δ⁻¹ * ∫ x, ‖V x‖ := by
    have h := Measure.integral_comp_mul_left (fun y => ‖V y‖) δ
    simpa [smul_eq_mul, abs_of_pos (inv_pos.mpr hδ)] using h
  calc ∫ x, ‖wtaubModDil V w₀ δ x‖
        = δ * ∫ x : ℝ, ‖V (δ * x)‖ := by
          rw [enorm]
          exact integral_const_mul _ _
      _ = ∫ x, ‖V x‖ := by
          rw [hsub, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hδ), one_mul]

private theorem wtaub_modDil_fourier {V : ℝ → ℂ} (_hV : Integrable V volume)
    (w₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (wtaubModDil V w₀ δ) ξ = 𝓕 V ((ξ - w₀) / δ) := by
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
  have hmod : 𝓕 (wtaubModDil V w₀ δ) ξ =
      𝓕 (fun x => (δ : ℂ) * V (δ * x)) (ξ - w₀) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq]
    congr 1
    ext x
    have harg : -(x * ξ) + w₀ * x = -(x * (ξ - w₀)) := by ring
    have hchar : ((Real.fourierChar (-(x * ξ)) : Circle) : ℂ) *
          ((Real.fourierChar (w₀ * x) : Circle) : ℂ) =
        ((Real.fourierChar (-(x * (ξ - w₀))) : Circle) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, harg]
    calc Real.fourierChar (-(x * ξ)) • wtaubModDil V w₀ δ x
          = ((Real.fourierChar (-(x * ξ)) : Circle) : ℂ) *
            (wtaubModDil V w₀ δ x) := by
            rw [Circle.smul_def, smul_eq_mul]
        _ = ((Real.fourierChar (-(x * ξ)) : Circle) : ℂ) *
            (((Real.fourierChar (w₀ * x) : Circle) : ℂ) *
              ((δ : ℂ) * V (δ * x))) := rfl
        _ = (((Real.fourierChar (-(x * ξ)) : Circle) : ℂ) *
            ((Real.fourierChar (w₀ * x) : Circle) : ℂ)) *
            ((δ : ℂ) * V (δ * x)) := by ring
        _ = ((Real.fourierChar (-(x * (ξ - w₀))) : Circle) : ℂ) *
            ((δ : ℂ) * V (δ * x)) := by rw [hchar]
        _ = Real.fourierChar (-(x * (ξ - w₀))) • ((δ : ℂ) * V (δ * x)) := by
            rw [Circle.smul_def, smul_eq_mul]
  have hdil : 𝓕 (fun x => (δ : ℂ) * V (δ * x)) (ξ - w₀) =
      𝓕 V ((ξ - w₀) / δ) := by
    rw [wtaub_fourier_const_mul, Real.fourier_comp_mul_left_of_pos _ hδ,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hδc, one_mul]
  rw [hmod, hdil]

-- L¹ Fourier uniqueness.
private theorem wtaub_test_weight {g : ℝ → ℝ}
    (hg_diff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hg_supp : HasCompactSupport g) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ Integrable ψ volume ∧
      (∀ ξ : ℝ, 𝓕 ψ ξ = Complex.ofRealCLM (g ξ)) := by
  have hφdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg_diff
  have hφsupp : HasCompactSupport (⇑Complex.ofRealCLM ∘ g) :=
    hg_supp.comp_left (by simp)
  refine ⟨⇑(FourierTransformInv.fourierInv (hφsupp.toSchwartzMap hφdiff)),
    (FourierTransformInv.fourierInv
      (hφsupp.toSchwartzMap hφdiff)).continuous,
    (FourierTransformInv.fourierInv
      (hφsupp.toSchwartzMap hφdiff)).integrable, ?_⟩
  intro ξ
  have hpair := FourierInvPair.fourier_fourierInv_eq
    (E := SchwartzMap ℝ ℂ) (F := SchwartzMap ℝ ℂ)
    (hφsupp.toSchwartzMap hφdiff)
  calc 𝓕 (⇑(FourierTransformInv.fourierInv
          (hφsupp.toSchwartzMap hφdiff))) ξ
        = ⇑(FourierTransform.fourier (FourierTransformInv.fourierInv
          (hφsupp.toSchwartzMap hφdiff))) ξ := by
          rw [SchwartzMap.fourier_coe]
      _ = ⇑(hφsupp.toSchwartzMap hφdiff) ξ := by rw [hpair]
      _ = Complex.ofRealCLM (g ξ) :=
          HasCompactSupport.toSchwartzMap_toFun hφsupp hφdiff ξ

private theorem wtaub_ae_zero {u : ℝ → ℂ} (hu : Integrable u volume)
    (h : ∀ ξ : ℝ, 𝓕 u ξ = 0) : u =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable
    fun g hg_diff hg_supp => ?_
  obtain ⟨ψ, hψcont, hψint, hψF⟩ := wtaub_test_weight hg_diff hg_supp
  have hint : ∀ x : ℝ, g x • u x = (𝓕 ψ x) * u x := by
    intro x
    have e : (𝓕 ψ x) = ((g x : ℝ) : ℂ) := by
      rw [hψF x, Complex.ofRealCLM_apply]
    rw [e]
    exact RCLike.real_smul_eq_coe_mul _ _
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.fourierChar (-(p.2 * p.1)) • ψ p.2) * u p.1)
      (volume.prod volume) := by
    have hc : Continuous fun p : ℝ × ℝ => Real.fourierChar (-(p.2 * p.1)) :=
      Real.continuous_fourierChar.comp ((continuous_snd.mul continuous_fst).neg)
    exact (hc.aestronglyMeasurable.smul
      (hψcont.comp continuous_snd).aestronglyMeasurable).mul
      hu.aestronglyMeasurable.comp_fst
  have hFnorm : Integrable
      (fun p : ℝ × ℝ => (Real.fourierChar (-(p.2 * p.1)) • ψ p.2) * u p.1)
      (volume.prod volume) := by
    rw [← integrable_norm_iff hFmeas]
    have enorm : (fun p : ℝ × ℝ =>
          ‖(Real.fourierChar (-(p.2 * p.1)) • ψ p.2) * u p.1‖) =
        fun p : ℝ × ℝ => ‖u p.1‖ * ‖ψ p.2‖ := by
      ext p
      rw [norm_mul, Circle.norm_smul]
      exact mul_comm _ _
    rw [enorm]
    exact hu.norm.mul_prod hψint.norm
  have hswap : (∫ x, ∫ v, (Real.fourierChar (-(v * x)) • ψ v) * u x) =
      (∫ v, ∫ x, (Real.fourierChar (-(v * x)) • ψ v) * u x) := by
    have hU : Integrable
        (Function.uncurry fun x v => (Real.fourierChar (-(v * x)) • ψ v) * u x)
        (volume.prod volume) := hFnorm
    exact MeasureTheory.integral_integral_swap hU
  have hinner : ∀ v : ℝ,
      (∫ x, (Real.fourierChar (-(v * x)) • ψ v) * u x) = 0 := by
    intro v
    have e1 : ∀ x : ℝ, (Real.fourierChar (-(v * x)) • ψ v) * u x =
        ψ v * (Real.fourierChar (-(x * v)) • u x) := by
      intro x
      have hcomm : -(v * x) = -(x * v) := by ring
      rw [hcomm]
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    rw [integral_congr_ae (ae_of_all _ e1), integral_const_mul,
      ← Real.fourier_real_eq, h v, mul_zero]
  calc ∫ x, g x • u x
        = ∫ x, (𝓕 ψ x) * u x := integral_congr_ae (ae_of_all _ hint)
      _ = ∫ x, ∫ v, (Real.fourierChar (-(v * x)) • ψ v) * u x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Real.fourier_real_eq]
          exact (integral_mul_const _ _).symm
      _ = ∫ v, ∫ x, (Real.fourierChar (-(v * x)) • ψ v) * u x := hswap
      _ = 0 := by simp only [hinner, integral_zero]

-- Local smallness estimate.
private theorem wtaub_modDil_sub {V : ℝ → ℂ} (w₀ : ℝ) {δ : ℝ}
    (Vδ : ℝ → ℂ) (hVδeq : ∀ z : ℝ, Vδ z = V (δ * z)) (x y : ℝ) :
    wtaubModDil V w₀ δ (x - y) -
      ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * wtaubModDil V w₀ δ x =
      ((Real.fourierChar (w₀ * (x - y)) : Circle) : ℂ) *
        ((δ : ℂ) * (Vδ (x - y) - Vδ x)) := by
  have hchar : ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) *
      ((Real.fourierChar (w₀ * x) : Circle) : ℂ) =
      ((Real.fourierChar (w₀ * (x - y)) : Circle) : ℂ) := by
    have harg : -(y * w₀) + w₀ * x = w₀ * (x - y) := by ring
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, harg]
  change ((Real.fourierChar (w₀ * (x - y)) : Circle) : ℂ) * ((δ : ℂ) * V (δ * (x - y))) -
      ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) *
        (((Real.fourierChar (w₀ * x) : Circle) : ℂ) * ((δ : ℂ) * V (δ * x))) =
      ((Real.fourierChar (w₀ * (x - y)) : Circle) : ℂ) *
        ((δ : ℂ) * (Vδ (x - y) - Vδ x))
  simp only [hVδeq]
  linear_combination (-((δ : ℂ) * V (δ * x))) * hchar

private theorem wtaub_local_small_norm {V : ℝ → ℂ} (w₀ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (Vδ : ℝ → ℂ) (hVδeq : ∀ z : ℝ, Vδ z = V (δ * z)) (a : ℂ) (x y : ℝ) :
    ‖a * (wtaubModDil V w₀ δ (x - y) -
      ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * wtaubModDil V w₀ δ x)‖ =
      ‖a‖ * (δ * ‖Vδ (x - y) - Vδ x‖) := by
  rw [wtaub_modDil_sub w₀ Vδ hVδeq x y, norm_mul, norm_mul, Circle.norm_coe,
    one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]

private theorem wtaub_local_small_rep {f V : ℝ → ℂ} (hf : Integrable f volume)
    (hV : Integrable V volume) (w₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x : ℝ ∂volume,
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ δ)) x -
        𝓕 f w₀ * wtaubModDil V w₀ δ x =
      ∫ y, f y * (wtaubModDil V w₀ δ (x - y) -
        ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * wtaubModDil V w₀ δ x) := by
  have hW : Integrable (wtaubModDil V w₀ δ) volume :=
    wtaub_modDil_integrable hV w₀ hδ
  have ha : 𝓕 f w₀ =
      ∫ y, ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * f y := by
    rw [Real.fourier_real_eq]
    apply integral_congr_ae
    filter_upwards with y
    rw [Circle.smul_def, smul_eq_mul]
  have hcc : Continuous
      fun y : ℝ => ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const).neg)
  have hcf : Integrable
      (fun y : ℝ => ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * f y)
      volume :=
    hf.bdd_mul hcc.aestronglyMeasurable
      (ae_of_all _ fun y => le_of_eq (Circle.norm_coe _))
  filter_upwards [hf.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ) hW]
    with x hx
  have h1L : Integrable
      (fun y => (ContinuousLinearMap.mul ℂ ℂ) (f y) (wtaubModDil V w₀ δ (x - y)))
      volume := hx
  have hJ : Integrable
      (fun y => ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * f y *
        wtaubModDil V w₀ δ x) volume :=
    hcf.mul_const _
  have e1 : (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ δ)) x =
      ∫ y, (ContinuousLinearMap.mul ℂ ℂ) (f y) (wtaubModDil V w₀ δ (x - y)) := by
    rw [MeasureTheory.convolution_def]
  have e2 : 𝓕 f w₀ * wtaubModDil V w₀ δ x =
      ∫ y, ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * f y *
        wtaubModDil V w₀ δ x := by
    rw [ha, integral_mul_const]
  have eSub : (∫ y, (ContinuousLinearMap.mul ℂ ℂ) (f y)
        (wtaubModDil V w₀ δ (x - y))) -
      (∫ y, ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * f y *
        wtaubModDil V w₀ δ x) =
      ∫ y, f y * (wtaubModDil V w₀ δ (x - y) -
        ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * wtaubModDil V w₀ δ x) := by
    rw [← integral_sub h1L hJ]
    congr 1
    ext y
    rw [ContinuousLinearMap.mul_apply']
    ring
  rw [e1, e2]
  exact eSub

private theorem wtaub_local_small {f V : ℝ → ℂ} (hf : Integrable f volume)
    (hV : Integrable V volume) (w₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ δ)) x -
        𝓕 f w₀ * wtaubModDil V w₀ δ x‖ ≤
      ∫ y, ‖f y‖ * ∫ x, ‖V (x - δ * y) - V x‖ := by
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hW : Integrable (wtaubModDil V w₀ δ) volume :=
    wtaub_modDil_integrable hV w₀ hδ
  set Vδ : ℝ → ℂ := fun z => V (δ * z) with hVδdef
  have hVδ : Integrable Vδ volume := hV.comp_mul_left' hδne
  have hVδeq : ∀ z : ℝ, Vδ z = V (δ * z) := fun z => rfl
  have hdiff : Integrable
      (fun x => (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ δ)) x -
        𝓕 f w₀ * wtaubModDil V w₀ δ x) volume :=
    (wtaub_conv_integrable hf hW).sub (hW.const_mul _)
  have hBslice : ∀ y : ℝ,
      Integrable (fun x => ‖f y‖ * (δ * ‖Vδ (x - y) - Vδ x‖)) volume := by
    intro y
    have hsub : Integrable (fun x => Vδ (x - y) - Vδ x) volume :=
      (hVδ.comp_sub_right y).sub hVδ
    exact (hsub.norm.const_mul δ).const_mul (‖f y‖)
  have hωmeas : AEStronglyMeasurable
      (fun y => ∫ x, ‖V (x - δ * y) - V x‖) volume :=
    ((wtaub_translate_continuous hV).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hωbound : ∀ᵐ y : ℝ ∂volume,
      ‖∫ x, ‖V (x - δ * y) - V x‖‖ ≤ 2 * ∫ x, ‖V x‖ := by
    filter_upwards with y
    have hb := wtaub_translate_bound hV (δ * y)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hBout : Integrable (fun y => ‖f y‖ * ∫ x, ‖V (x - δ * y) - V x‖) volume :=
    hf.norm.mul_bdd hωmeas hωbound
  have hper : ∀ y : ℝ, (∫ x, ‖f y‖ * (δ * ‖Vδ (x - y) - Vδ x‖)) =
      ‖f y‖ * ∫ x, ‖V (x - δ * y) - V x‖ := by
    intro y
    have hcc1 : (∫ x, ‖f y‖ * (δ * ‖Vδ (x - y) - Vδ x‖)) =
        ‖f y‖ * (δ * ∫ x, ‖Vδ (x - y) - Vδ x‖) := by
      rw [integral_const_mul, integral_const_mul]
    have hsub : (∫ x, ‖Vδ (x - y) - Vδ x‖) =
        δ⁻¹ * ∫ x, ‖V (x - δ * y) - V x‖ := by
      have h2 : ∀ x : ℝ, ‖Vδ (x - y) - Vδ x‖ =
          ‖V (δ * x - δ * y) - V (δ * x)‖ := by
        intro x
        change ‖V (δ * (x - y)) - V (δ * x)‖ = _
        rw [mul_sub]
      rw [integral_congr_ae (ae_of_all _ h2)]
      have h := Measure.integral_comp_mul_left (fun z => ‖V (z - δ * y) - V z‖) δ
      simpa [smul_eq_mul, abs_of_pos (inv_pos.mpr hδ)] using h
    rw [hcc1, hsub, show δ * (δ⁻¹ * ∫ x, ‖V (x - δ * y) - V x‖) =
      ∫ x, ‖V (x - δ * y) - V x‖ from by
        rw [← mul_assoc, mul_inv_cancel₀ hδne, one_mul]]
  have hnormB : ∀ x y : ℝ,
      ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖ =
      ‖f y‖ * (δ * ‖Vδ (x - y) - Vδ x‖) := by
    intro x y
    have hnn : 0 ≤ (fun p : ℝ × ℝ =>
        ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y) := by
      change 0 ≤ ‖f y‖ * (δ * ‖Vδ (x - y) - Vδ x‖)
      exact mul_nonneg (norm_nonneg _) (mul_nonneg hδ.le (norm_nonneg _))
    rw [Real.norm_of_nonneg hnn]
  have hVf : AEStronglyMeasurable (fun p : ℝ × ℝ => Vδ (p.1 - p.2))
      (volume.prod volume) := by
    have hmap : AEStronglyMeasurable Vδ
        (Measure.map (fun p : ℝ × ℝ => p.1 - p.2) (volume.prod volume)) :=
      hVδ.aestronglyMeasurable.mono_ac
        (quasiMeasurePreserving_sub_of_right_invariant volume volume).absolutelyContinuous
    exact hmap.comp_measurable measurable_sub
  have hBpmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖))
      (volume.prod volume) :=
    (hf.aestronglyMeasurable.comp_snd.norm).mul
      (((hVf.sub hVδ.aestronglyMeasurable.comp_fst).norm).const_mul δ)
  have hBprod : Integrable
      (fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖))
      (volume.prod volume) := by
    rw [integrable_prod_iff' hBpmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards with y
      exact hBslice y
    · have h2 : (fun y => ∫ x,
          ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖) =
          (fun y => ‖f y‖ * ∫ x, ‖V (x - δ * y) - V x‖) := by
        funext y
        rw [integral_congr_ae (ae_of_all _ fun x => hnormB x y)]
        exact hper y
      rw [h2]
      exact hBout
  have hG : Integrable
      (fun x => ∫ y,
        ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖)
      volume :=
    ((integrable_prod_iff hBpmeas).mp hBprod).2
  have hswap : (∫ x, ∫ y,
        ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖) =
      (∫ y, ∫ x,
        ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖) := by
    have hU : Integrable
        (Function.uncurry fun x y =>
          ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖)
        (volume.prod volume) := hBprod.norm
    exact MeasureTheory.integral_integral_swap hU
  have hDBeq : ∀ x y : ℝ, ‖f y * (wtaubModDil V w₀ δ (x - y) -
      ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) * wtaubModDil V w₀ δ x)‖ =
      ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖ := by
    intro x y
    rw [wtaub_local_small_norm w₀ hδ Vδ hVδeq (f y) x y]
    exact (hnormB x y).symm
  have hle : ∀ᵐ x : ℝ ∂volume, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (wtaubModDil V w₀ δ)) x - 𝓕 f w₀ * wtaubModDil V w₀ δ x‖ ≤
      ∫ y, ‖(fun p : ℝ × ℝ => ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖ := by
    filter_upwards [wtaub_local_small_rep hf hV w₀ hδ] with x hx
    calc ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ δ)) x -
            𝓕 f w₀ * wtaubModDil V w₀ δ x‖
          = ‖∫ y, f y * (wtaubModDil V w₀ δ (x - y) -
            ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) *
              wtaubModDil V w₀ δ x)‖ := by rw [hx]
        _ ≤ ∫ y, ‖f y * (wtaubModDil V w₀ δ (x - y) -
            ((Real.fourierChar (-(y * w₀)) : Circle) : ℂ) *
              wtaubModDil V w₀ δ x)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ y, ‖(fun p : ℝ × ℝ =>
            ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖ :=
            integral_congr_ae (ae_of_all _ fun y => hDBeq x y)
  calc ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ δ)) x -
          𝓕 f w₀ * wtaubModDil V w₀ δ x‖
        ≤ ∫ x, ∫ y, ‖(fun p : ℝ × ℝ =>
            ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖ :=
          integral_mono_ae hdiff.norm hG hle
      _ = ∫ y, ∫ x, ‖(fun p : ℝ × ℝ =>
            ‖f p.2‖ * (δ * ‖Vδ (p.1 - p.2) - Vδ p.1‖)) (x, y)‖ := hswap
      _ = ∫ y, ‖f y‖ * ∫ x, ‖V (x - δ * y) - V x‖ := by
          apply integral_congr_ae
          filter_upwards with y
          rw [integral_congr_ae (ae_of_all _ fun x => hnormB x y)]
          exact hper y

-- Approximate identity bound and corollary.
private theorem wtaub_approx_id_rep {W g : ℝ → ℂ} (hW : Integrable W volume)
    (hg : Integrable g volume) (h1 : ∫ x, W x = 1) {lam : ℝ} (hlam : 0 < lam) :
    ∀ᵐ x : ℝ ∂volume, ((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - g x =
      ∫ u, ((lam : ℂ) * W (lam * u)) * (g (x - u) - g x) := by
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hWl : Integrable (wtaubDil W lam) volume :=
    (hW.comp_mul_left' hlamne).const_mul _
  have hint1 : (∫ t, (lam : ℂ) * W (lam * t)) = 1 := by
    have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlamne
    have h := Measure.integral_comp_mul_left W lam
    rw [integral_const_mul, h, h1, RCLike.real_smul_eq_coe_mul, mul_one,
      abs_of_pos (inv_pos.mpr hlam), RCLike.ofReal_inv]
    exact mul_inv_cancel₀ hlamc
  filter_upwards [hWl.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ) hg]
    with x hx
  have hHL : Integrable
      (fun t => (ContinuousLinearMap.mul ℂ ℂ) (wtaubDil W lam t) (g (x - t)))
      volume := hx
  have hHeq : ∀ t : ℝ, (wtaubDil W lam t) * g (x - t) =
      ((lam : ℂ) * W (lam * t)) * g (x - t) :=
    fun t => rfl
  have ept : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (wtaubDil W lam t) (g (x - t)) =
      ((lam : ℂ) * W (lam * t)) * g (x - t) := by
    intro t
    simpa only [ContinuousLinearMap.mul_apply'] using hHeq t
  have hH : Integrable (fun t => ((lam : ℂ) * W (lam * t)) * g (x - t)) volume :=
    hHL.congr (ae_of_all _ ept)
  have hGx : Integrable (fun t => ((lam : ℂ) * W (lam * t)) * g x) volume :=
    ((hW.comp_mul_left' hlamne).const_mul _).mul_const _
  have e1 : ((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x =
      ∫ t, ((lam : ℂ) * W (lam * t)) * g (x - t) := by
    rw [MeasureTheory.convolution_def]
    exact integral_congr_ae (ae_of_all _ ept)
  have e2 : g x = ∫ t, ((lam : ℂ) * W (lam * t)) * g x := by
    conv_rhs => rw [integral_mul_const]
    rw [hint1, one_mul]
  have eSub : (∫ t, ((lam : ℂ) * W (lam * t)) * g (x - t)) -
      (∫ t, ((lam : ℂ) * W (lam * t)) * g x) =
      ∫ u, ((lam : ℂ) * W (lam * u)) * (g (x - u) - g x) := by
    rw [← integral_sub hH hGx]
    congr 1
    ext t
    ring
  conv_lhs => rw [e1, e2]
  exact eSub

private theorem wtaub_approx_id {W g : ℝ → ℂ} (hW : Integrable W volume)
    (hg : Integrable g volume) (h1 : ∫ x, W x = 1) {lam : ℝ}
    (hlam : 0 < lam) :
    ∫ x, ‖((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - g x‖ ≤
      ∫ s, ‖W s‖ * ∫ x, ‖g (x - lam⁻¹ * s) - g x‖ := by
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hWl : Integrable (wtaubDil W lam) volume :=
    (hW.comp_mul_left' hlamne).const_mul _
  have hWl2 : Integrable (fun v => W (lam * v)) volume :=
    hW.comp_mul_left' hlamne
  have hWt : Integrable (fun u => lam * ‖W (lam * u)‖) volume :=
    (hW.norm.comp_mul_left' hlamne).const_mul lam
  have hdiff : Integrable
      (fun x => ((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - g x)
      volume :=
    (wtaub_conv_integrable hWl hg).sub hg
  have hnorm : ∀ x u : ℝ, ‖((lam : ℂ) * W (lam * u)) * (g (x - u) - g x)‖ =
      (lam * ‖W (lam * u)‖) * ‖g (x - u) - g x‖ := by
    intro x u
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  have hBslice : ∀ u : ℝ,
      Integrable (fun x => (lam * ‖W (lam * u)‖) * ‖g (x - u) - g x‖) volume := by
    intro u
    have hsub : Integrable (fun x => g (x - u) - g x) volume :=
      (hg.comp_sub_right u).sub hg
    exact hsub.norm.const_mul _
  have hωmeas : AEStronglyMeasurable
      (fun u => ∫ x, ‖g (x - u) - g x‖) volume :=
    (wtaub_translate_continuous hg).aestronglyMeasurable
  have hωbound : ∀ᵐ u : ℝ ∂volume,
      ‖∫ x, ‖g (x - u) - g x‖‖ ≤ 2 * ∫ x, ‖g x‖ := by
    filter_upwards with u
    have hb := wtaub_translate_bound hg u
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hBout : Integrable
      (fun u => (lam * ‖W (lam * u)‖) * ∫ x, ‖g (x - u) - g x‖) volume :=
    hWt.mul_bdd hωmeas hωbound
  have hper : ∀ u : ℝ, (∫ x, (lam * ‖W (lam * u)‖) * ‖g (x - u) - g x‖) =
      (lam * ‖W (lam * u)‖) * ∫ x, ‖g (x - u) - g x‖ :=
    fun u => integral_const_mul _ _
  have hnormB : ∀ x u : ℝ,
      ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
        ‖g (p.1 - p.2) - g p.1‖) (x, u)‖ =
      (lam * ‖W (lam * u)‖) * ‖g (x - u) - g x‖ := by
    intro x u
    have hnn : 0 ≤ (fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
        ‖g (p.1 - p.2) - g p.1‖) (x, u) := by
      change 0 ≤ (lam * ‖W (lam * u)‖) * ‖g (x - u) - g x‖
      exact mul_nonneg (mul_nonneg hlam.le (norm_nonneg _)) (norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
  have hGsub : AEStronglyMeasurable (fun p : ℝ × ℝ => g (p.1 - p.2))
      (volume.prod volume) := by
    have hmap : AEStronglyMeasurable g
        (Measure.map (fun p : ℝ × ℝ => p.1 - p.2) (volume.prod volume)) :=
      hg.aestronglyMeasurable.mono_ac
        (quasiMeasurePreserving_sub_of_right_invariant volume volume).absolutelyContinuous
    exact hmap.comp_measurable measurable_sub
  have hBpmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
        ‖g (p.1 - p.2) - g p.1‖)
      (volume.prod volume) :=
    (((hWl2.aestronglyMeasurable.comp_snd).norm).const_mul lam).mul
      (((hGsub.sub hg.aestronglyMeasurable.comp_fst).norm))
  have hBprod : Integrable
      (fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
        ‖g (p.1 - p.2) - g p.1‖)
      (volume.prod volume) := by
    rw [integrable_prod_iff' hBpmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards with u
      exact hBslice u
    · have h2 : (fun u => ∫ x,
          ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
            ‖g (p.1 - p.2) - g p.1‖) (x, u)‖) =
          (fun u => (lam * ‖W (lam * u)‖) * ∫ x, ‖g (x - u) - g x‖) := by
        funext u
        rw [integral_congr_ae (ae_of_all _ fun x => hnormB x u)]
        exact hper u
      rw [h2]
      exact hBout
  have hG : Integrable
      (fun x => ∫ u,
        ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
          ‖g (p.1 - p.2) - g p.1‖) (x, u)‖)
      volume :=
    ((integrable_prod_iff hBpmeas).mp hBprod).2
  have hswap : (∫ x, ∫ u,
        ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
          ‖g (p.1 - p.2) - g p.1‖) (x, u)‖) =
      (∫ u, ∫ x,
        ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
          ‖g (p.1 - p.2) - g p.1‖) (x, u)‖) := by
    have hU : Integrable
        (Function.uncurry fun x u =>
          ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
            ‖g (p.1 - p.2) - g p.1‖) (x, u)‖)
        (volume.prod volume) := hBprod.norm
    exact MeasureTheory.integral_integral_swap hU
  have hDBeq : ∀ x u : ℝ, ‖((lam : ℂ) * W (lam * u)) * (g (x - u) - g x)‖ =
      ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
        ‖g (p.1 - p.2) - g p.1‖) (x, u)‖ := by
    intro x u
    rw [hnorm x u]
    exact (hnormB x u).symm
  have hle : ∀ᵐ x : ℝ ∂volume, ‖((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
      g x‖ ≤
      ∫ u, ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
        ‖g (p.1 - p.2) - g p.1‖) (x, u)‖ := by
    filter_upwards [wtaub_approx_id_rep hW hg h1 hlam] with x hx
    calc ‖((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - g x‖
          = ‖∫ u, ((lam : ℂ) * W (lam * u)) * (g (x - u) - g x)‖ := by rw [hx]
        _ ≤ ∫ u, ‖((lam : ℂ) * W (lam * u)) * (g (x - u) - g x)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ u, ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
            ‖g (p.1 - p.2) - g p.1‖) (x, u)‖ :=
            integral_congr_ae (ae_of_all _ fun u => hDBeq x u)
  have hback : (∫ u, (lam * ‖W (lam * u)‖) * ∫ x, ‖g (x - u) - g x‖) =
      ∫ s, ‖W s‖ * ∫ x, ‖g (x - lam⁻¹ * s) - g x‖ := by
    have hpt : ∀ t : ℝ, (fun s => ‖W s‖ * ∫ x, ‖g (x - lam⁻¹ * s) - g x‖) (lam * t) =
        ‖W (lam * t)‖ * ∫ x, ‖g (x - t) - g x‖ := by
      intro t
      change ‖W (lam * t)‖ * ∫ x, ‖g (x - lam⁻¹ * (lam * t)) - g x‖ = _
      rw [show lam⁻¹ * (lam * t) = t from by
        rw [← mul_assoc, inv_mul_cancel₀ hlamne, one_mul]]
    have h := Measure.integral_comp_mul_left
      (fun s => ‖W s‖ * ∫ x, ‖g (x - lam⁻¹ * s) - g x‖) lam
    rw [integral_congr_ae (ae_of_all _ hpt)] at h
    have eL : (∫ u, (lam * ‖W (lam * u)‖) * ∫ x, ‖g (x - u) - g x‖) =
        lam * ∫ u, ‖W (lam * u)‖ * ∫ x, ‖g (x - u) - g x‖ := by
      have e1 : ∀ u : ℝ, (lam * ‖W (lam * u)‖) * ∫ x, ‖g (x - u) - g x‖ =
          lam * (‖W (lam * u)‖ * ∫ x, ‖g (x - u) - g x‖) :=
        fun u => mul_assoc _ _ _
      rw [integral_congr_ae (ae_of_all _ e1)]
      exact integral_const_mul _ _
    rw [eL, h, smul_eq_mul, abs_of_pos (inv_pos.mpr hlam),
      mul_inv_cancel_left₀ hlamne]
  calc ∫ x, ‖((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - g x‖
        ≤ ∫ x, ∫ u, ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
            ‖g (p.1 - p.2) - g p.1‖) (x, u)‖ :=
          integral_mono_ae hdiff.norm hG hle
      _ = ∫ u, ∫ x, ‖(fun p : ℝ × ℝ => (lam * ‖(fun v => W (lam * v)) p.2‖) *
            ‖g (p.1 - p.2) - g p.1‖) (x, u)‖ := hswap
      _ = ∫ s, ‖W s‖ * ∫ x, ‖g (x - lam⁻¹ * s) - g x‖ := by
          rw [← hback]
          apply integral_congr_ae
          filter_upwards with u
          rw [integral_congr_ae (ae_of_all _ fun x => hnormB x u)]
          exact hper u

private theorem wtaub_approx_id_small {W g : ℝ → ℂ} (hW : Integrable W volume)
    (hg : Integrable g volume) (h1 : ∫ x, W x = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧
      ∫ x, ‖((wtaubDil W lam) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - g x‖ < ε := by
  have hlim := wtaub_dilation_limit hW hg
  obtain ⟨d, hdpos, hd⟩ :=
    Metric.eventually_nhds_iff.mp ((Metric.tendsto_nhds.mp hlim) ε hε)
  refine ⟨2 / d, by positivity, ?_⟩
  have hlam : (0 : ℝ) < 2 / d := by positivity
  have hdist : dist ((2 / d)⁻¹) 0 < d := by
    rw [dist_zero_right, Real.norm_eq_abs, inv_div, abs_of_nonneg (half_pos hdpos).le]
    linarith
  have hΦ := hd hdist
  have hnn : 0 ≤ ∫ s, ‖W s‖ * ∫ x, ‖g (x - (2 / d)⁻¹ * s) - g x‖ :=
    integral_nonneg_of_ae (ae_of_all _ fun s =>
      mul_nonneg (norm_nonneg _)
        (integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)))
  rw [dist_zero_right, Real.norm_of_nonneg hnn] at hΦ
  have hΦ' : (∫ s, ‖W s‖ * ∫ x, ‖g (x - (2 / d)⁻¹ * s) - g x‖) < ε := hΦ
  exact (wtaub_approx_id hW hg h1 hlam).trans_lt hΦ'

-- Neumann series for convolution.
private theorem wtaub_neumann_pow {u v : ℝ → ℂ} (hu : Integrable u volume)
    (hv : Integrable v volume) (n : ℕ) :
    Integrable ((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) volume ∧
    ∫ x, ‖((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) x‖ ≤
      (∫ x, ‖u x‖)^n * ∫ x, ‖v x‖ := by
  induction n with
  | zero =>
    have e0 : (fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[0] v = v :=
      congrFun (Function.iterate_zero _) _
    rw [e0]
    exact ⟨hv, by simp⟩
  | succ n ih =>
    have e : (fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n + 1] v =
        u ⋆[ContinuousLinearMap.mul ℂ ℂ]
          ((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) :=
      Function.iterate_succ_apply' _ _ _
    have hconv := wtaub_conv_integrable hu ih.1
    have hqnn : 0 ≤ ∫ x, ‖u x‖ :=
      integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left ih.2 hqnn
    have heq : (∫ x, ‖u x‖) * ((∫ x, ‖u x‖)^n * ∫ x, ‖v x‖) =
        (∫ x, ‖u x‖)^(n + 1) * ∫ x, ‖v x‖ := by
      rw [pow_succ]
      ring
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hconv
    · rw [e]
      refine (wtaub_conv_norm_le hu ih.1).trans ?_
      rw [← heq]
      exact hmul

private theorem wtaub_neumann_fourier {u v : ℝ → ℂ} (hu : Integrable u volume)
    (hv : Integrable v volume) (n : ℕ) (ξ : ℝ) :
    𝓕 ((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) ξ =
      (𝓕 u ξ)^n * 𝓕 v ξ := by
  induction n with
  | zero =>
    simp [Function.iterate_zero]
  | succ n ih =>
    have e : (fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n + 1] v =
        u ⋆[ContinuousLinearMap.mul ℂ ℂ]
          ((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) :=
      Function.iterate_succ_apply' _ _ _
    rw [e, Real.fourier_mul_convolution_eq hu (wtaub_neumann_pow hu hv n).1, ih,
      pow_succ]
    ring

private theorem wtaub_neumann {u v : ℝ → ℂ} (hu : Integrable u volume)
    (hv : Integrable v volume) (h : ∫ x, ‖u x‖ < 1) :
    ∃ S : ℝ → ℂ, Integrable S volume ∧ (∀ ξ : ℝ, 1 - 𝓕 u ξ ≠ 0) ∧
      ∀ ξ : ℝ, 𝓕 S ξ = 𝓕 v ξ / (1 - 𝓕 u ξ) := by
  have hqnn : 0 ≤ ∫ x, ‖u x‖ :=
    integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
  have hq1 : ‖(∫ x, ‖u x‖)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hqnn]
    exact h
  have hFbound : ∀ ξ : ℝ, ‖𝓕 u ξ‖ ≤ ∫ x, ‖u x‖ := by
    intro ξ
    have e : ∀ x : ℝ, ‖Real.fourierChar (-(x * ξ)) • u x‖ = ‖u x‖ :=
      fun x => Circle.norm_smul _ _
    rw [Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [integral_congr_ae (ae_of_all _ e)]
  have hne : ∀ ξ : ℝ, 1 - 𝓕 u ξ ≠ 0 := by
    intro ξ h0
    have h1 : 𝓕 u ξ = 1 := by
      rw [sub_eq_zero] at h0
      exact h0.symm
    have hlt := lt_of_le_of_lt (hFbound ξ) h
    rw [h1, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hmem : ∀ n : ℕ,
      MemLp ((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) 1 volume :=
    fun n => memLp_one_iff_integrable.mpr (wtaub_neumann_pow hu hv n).1
  have hnormLp : ∀ n : ℕ, ‖(hmem n).toLp‖ ≤ (∫ x, ‖u x‖)^n * ∫ x, ‖v x‖ := by
    intro n
    have haeN : (fun x =>
          ‖(((hmem n).toLp : Lp ℂ 1 volume) : ℝ → ℂ) x‖) =ᵐ[volume]
        (fun x => ‖((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) x‖) :=
      (hmem n).coeFn_toLp.mono fun x hx => congrArg _ hx
    rw [MeasureTheory.L1.norm_eq_integral_norm, integral_congr_ae haeN]
    exact (wtaub_neumann_pow hu hv n).2
  have hgeo : Summable fun n : ℕ => (∫ x, ‖u x‖)^n * ∫ x, ‖v x‖ :=
    (summable_geometric_of_norm_lt_one hq1).mul_right _
  have hsum : Summable fun n : ℕ => (hmem n).toLp :=
    Summable.of_norm_bounded hgeo hnormLp
  refine ⟨↑(∑' n, (hmem n).toLp), MeasureTheory.L1.integrable_coeFn _, ?_, ?_⟩
  · exact hne
  · intro ξ
    set Tξ : (Lp ℂ 1 volume) →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ ξ) ∘L
        (Real.Lp.fourierTransformCLM ℝ ℂ) with hTξ
    have hterm : ∀ n : ℕ, Tξ ((hmem n).toLp) =
        𝓕 ((fun w => u ⋆[ContinuousLinearMap.mul ℂ ℂ] w)^[n] v) ξ := by
      intro n
      have hft := congrFun (Real.fourierTransform_toLp (hmem n)) ξ
      rw [hTξ]
      simpa only [ContinuousLinearMap.comp_apply,
        Real.Lp.fourierTransformCLM_apply, BoundedContinuousFunction.evalCLM_apply]
        using hft
    have hmap : Tξ (∑' n, (hmem n).toLp) = ∑' n, Tξ ((hmem n).toLp) :=
      ContinuousLinearMap.map_tsum Tξ hsum
    have hgeom : (∑' n : ℕ, (𝓕 u ξ)^n) = (1 - 𝓕 u ξ)⁻¹ :=
      tsum_geometric_of_norm_lt_one (lt_of_le_of_lt (hFbound ξ) h)
    have htsum : (∑' n, Tξ ((hmem n).toLp)) = (1 - 𝓕 u ξ)⁻¹ * 𝓕 v ξ := by
      have e1 : (∑' n, Tξ ((hmem n).toLp)) =
          ∑' n, ((𝓕 u ξ)^n * 𝓕 v ξ) := by
        apply tsum_congr
        intro n
        rw [hterm n]
        exact wtaub_neumann_fourier hu hv n ξ
      rw [e1, tsum_mul_right, hgeom]
    have hTS : Tξ (∑' n, (hmem n).toLp) =
        𝓕 ((↑(∑' n, (hmem n).toLp) : ℝ → ℂ)) ξ := by
      rw [hTξ]
      simp only [ContinuousLinearMap.comp_apply,
        Real.Lp.fourierTransformCLM_apply, BoundedContinuousFunction.evalCLM_apply,
        Real.Lp.fourierTransform_apply]
    rw [hTS] at hmap
    rw [hmap, htsum, div_eq_mul_inv, mul_comm]

-- Wiener's local inversion lemma.
private theorem wtaub_local_inverse {f : ℝ → ℂ} (hf : Integrable f volume)
    {w₀ : ℝ} (hw : 𝓕 f w₀ ≠ 0) :
    ∃ h : ℝ → ℂ, ∃ r : ℝ, 0 < r ∧ Integrable h volume ∧
      ∀ ξ : ℝ, |ξ - w₀| < r → 𝓕 f ξ * 𝓕 h ξ = 1 := by
  obtain ⟨V, _, hVint, _, hV1, _, _⟩ := wtaub_bump
  have hpos : 0 < ‖𝓕 f w₀‖ := norm_pos_iff.mpr hw
  have hlim := wtaub_dilation_limit hf hVint
  obtain ⟨d, hdpos, hd⟩ :=
    Metric.eventually_nhds_iff.mp ((Metric.tendsto_nhds.mp hlim) _ hpos)
  have hδ : (0 : ℝ) < d / 2 := half_pos hdpos
  have hdist : dist (d / 2) 0 < d := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (half_pos hdpos).le]
    linarith
  have hΦ := hd hdist
  have hnnΦ : 0 ≤ ∫ y, ‖f y‖ * ∫ x, ‖V (x - (d / 2) * y) - V x‖ :=
    integral_nonneg_of_ae (ae_of_all _ fun y =>
      mul_nonneg (norm_nonneg _)
        (integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)))
  rw [dist_zero_right, Real.norm_of_nonneg hnnΦ] at hΦ
  have hWδ : Integrable (wtaubModDil V w₀ (d / 2)) volume :=
    wtaub_modDil_integrable hVint w₀ hδ
  have hconv : Integrable
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) volume :=
    wtaub_conv_integrable hf hWδ
  have hsmall : (∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (wtaubModDil V w₀ (d / 2))) x - 𝓕 f w₀ * wtaubModDil V w₀ (d / 2) x‖) <
      ‖𝓕 f w₀‖ :=
    lt_of_le_of_lt (wtaub_local_small hf hVint w₀ hδ) hΦ
  have hu : Integrable (fun x => wtaubModDil V w₀ (d / 2) x - (𝓕 f w₀)⁻¹ *
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x) volume :=
    hWδ.sub (hconv.const_mul _)
  have hnorm_pt : ∀ x : ℝ, ‖wtaubModDil V w₀ (d / 2) x - (𝓕 f w₀)⁻¹ *
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x‖ =
      ‖𝓕 f w₀‖⁻¹ * ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (wtaubModDil V w₀ (d / 2))) x - 𝓕 f w₀ * wtaubModDil V w₀ (d / 2) x‖ := by
    intro x
    have e : wtaubModDil V w₀ (d / 2) x - (𝓕 f w₀)⁻¹ *
        (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x =
        (𝓕 f w₀)⁻¹ * (𝓕 f w₀ * wtaubModDil V w₀ (d / 2) x -
          (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
    rw [e, norm_mul, norm_inv, norm_sub_rev]
  have hInt_eq : (∫ x, ‖wtaubModDil V w₀ (d / 2) x - (𝓕 f w₀)⁻¹ *
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x‖) =
      ‖𝓕 f w₀‖⁻¹ * (∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (wtaubModDil V w₀ (d / 2))) x - 𝓕 f w₀ * wtaubModDil V w₀ (d / 2) x‖) := by
    simp only [hnorm_pt]
    exact integral_const_mul _ _
  have hlt : (∫ x, ‖wtaubModDil V w₀ (d / 2) x - (𝓕 f w₀)⁻¹ *
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x‖) < 1 := by
    rw [hInt_eq]
    calc ‖𝓕 f w₀‖⁻¹ * _ < ‖𝓕 f w₀‖⁻¹ * ‖𝓕 f w₀‖ :=
          mul_lt_mul_of_pos_left hsmall (inv_pos.mpr hpos)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  obtain ⟨S, hSint, hneU, hSeq⟩ := wtaub_neumann hu hWδ hlt
  have hFu : ∀ ξ : ℝ, 𝓕 (fun x => wtaubModDil V w₀ (d / 2) x - (𝓕 f w₀)⁻¹ *
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x) ξ =
      𝓕 (wtaubModDil V w₀ (d / 2)) ξ - (𝓕 f w₀)⁻¹ *
        (𝓕 f ξ * 𝓕 (wtaubModDil V w₀ (d / 2)) ξ) := by
    intro ξ
    rw [wtaub_fourier_sub hWδ (hconv.const_mul _) ξ,
      wtaub_fourier_const_mul _ _ ξ, Real.fourier_mul_convolution_eq hf hWδ]
  have hF1 : ∀ ξ : ℝ, |ξ - w₀| < d / 2 → 𝓕 (wtaubModDil V w₀ (d / 2)) ξ = 1 := by
    intro ξ hξ
    rw [wtaub_modDil_fourier hVint w₀ hδ ξ]
    apply hV1
    rw [abs_div, abs_of_pos hδ]
    exact le_of_lt ((div_lt_one hδ).mpr hξ)
  refine ⟨fun x => (𝓕 f w₀)⁻¹ * S x, d / 2, hδ, hSint.const_mul _, ?_⟩
  intro ξ hξ
  have hF1ξ := hF1 ξ hξ
  have e10 : 1 - 𝓕 (fun x => wtaubModDil V w₀ (d / 2) x - (𝓕 f w₀)⁻¹ *
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] (wtaubModDil V w₀ (d / 2))) x) ξ =
      (𝓕 f w₀)⁻¹ * 𝓕 f ξ := by
    rw [hFu ξ, hF1ξ]
    ring
  have hSeq1 : 𝓕 S ξ = 1 / ((𝓕 f w₀)⁻¹ * 𝓕 f ξ) := by
    rw [hSeq ξ, hF1ξ, e10]
  have hneAG : (𝓕 f w₀)⁻¹ * 𝓕 f ξ ≠ 0 := by
    rw [← e10]
    exact hneU ξ
  have hFh : 𝓕 (fun x => (𝓕 f w₀)⁻¹ * S x) ξ =
      (𝓕 f w₀)⁻¹ * (1 / ((𝓕 f w₀)⁻¹ * 𝓕 f ξ)) := by
    rw [wtaub_fourier_const_mul _ _ ξ, hSeq1]
  rw [hFh, one_div, ← mul_assoc, mul_comm (𝓕 f ξ) ((𝓕 f w₀)⁻¹),
    mul_inv_cancel₀ hneAG]

-- Gluing plus compactness.
private theorem wtaub_glue {f h₁ h₂ : ℝ → ℂ} (hf : Integrable f volume)
    (hh₁ : Integrable h₁ volume) (hh₂ : Integrable h₂ volume)
    {A B : Set ℝ} (e₁ : ∀ ξ ∈ A, 𝓕 f ξ * 𝓕 h₁ ξ = 1)
    (e₂ : ∀ ξ ∈ B, 𝓕 f ξ * 𝓕 h₂ ξ = 1) :
    ∃ h : ℝ → ℂ, Integrable h volume ∧ ∀ ξ ∈ A ∪ B, 𝓕 f ξ * 𝓕 h ξ = 1 := by
  have hfh1 : Integrable (f ⋆[ContinuousLinearMap.mul ℂ ℂ] h₁) volume :=
    wtaub_conv_integrable hf hh₁
  have h12 : Integrable
      ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] h₁) ⋆[ContinuousLinearMap.mul ℂ ℂ] h₂)
      volume :=
    wtaub_conv_integrable hfh1 hh₂
  refine ⟨fun x => h₁ x + h₂ x -
    ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] h₁) ⋆[ContinuousLinearMap.mul ℂ ℂ] h₂) x,
    (hh₁.add hh₂).sub h12, ?_⟩
  intro ξ hξ
  have e_sub : 𝓕 (fun x => h₁ x + h₂ x -
      ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] h₁) ⋆[ContinuousLinearMap.mul ℂ ℂ] h₂) x) ξ =
      𝓕 (fun x => h₁ x + h₂ x) ξ -
        𝓕 ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] h₁) ⋆[ContinuousLinearMap.mul ℂ ℂ] h₂) ξ :=
    wtaub_fourier_sub (hh₁.add hh₂) h12 ξ
  have e_add : 𝓕 (fun x => h₁ x + h₂ x) ξ = 𝓕 h₁ ξ + 𝓕 h₂ ξ :=
    wtaub_fourier_add hh₁ hh₂ ξ
  have e_conv : 𝓕 ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] h₁) ⋆[ContinuousLinearMap.mul ℂ ℂ] h₂) ξ =
      𝓕 f ξ * 𝓕 h₁ ξ * 𝓕 h₂ ξ := by
    rw [Real.fourier_mul_convolution_eq hfh1 hh₂,
      Real.fourier_mul_convolution_eq hf hh₁]
  have hF : 𝓕 (fun x => h₁ x + h₂ x -
      ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] h₁) ⋆[ContinuousLinearMap.mul ℂ ℂ] h₂) x) ξ =
      𝓕 h₁ ξ + 𝓕 h₂ ξ - 𝓕 f ξ * 𝓕 h₁ ξ * 𝓕 h₂ ξ := by
    rw [e_sub, e_add, e_conv]
  rw [hF]
  rcases hξ with hA | hB
  · have eA := e₁ ξ hA
    have hid : 𝓕 f ξ * (𝓕 h₁ ξ + 𝓕 h₂ ξ - 𝓕 f ξ * 𝓕 h₁ ξ * 𝓕 h₂ ξ)
        = 1 + (𝓕 f ξ * 𝓕 h₁ ξ - 1) * (1 - 𝓕 f ξ * 𝓕 h₂ ξ) := by ring
    rw [hid, eA, sub_self, zero_mul, add_zero]
  · have eB := e₂ ξ hB
    have hid : 𝓕 f ξ * (𝓕 h₁ ξ + 𝓕 h₂ ξ - 𝓕 f ξ * 𝓕 h₁ ξ * 𝓕 h₂ ξ)
        = 1 + (𝓕 f ξ * 𝓕 h₂ ξ - 1) * (1 - 𝓕 f ξ * 𝓕 h₁ ξ) := by ring
    rw [hid, eB, sub_self, zero_mul, add_zero]

private theorem wtaub_inverse_on_Icc {f : ℝ → ℂ} (hf : Integrable f volume)
    (hF : ∀ w : ℝ, 𝓕 f w ≠ 0) (R : ℝ) :
    ∃ h : ℝ → ℂ, Integrable h volume ∧
      ∀ ξ ∈ Set.Icc (-R) R, 𝓕 f ξ * 𝓕 h ξ = 1 := by
  have hloc : ∀ w : ℝ, ∃ h : ℝ → ℂ, ∃ r : ℝ, 0 < r ∧ Integrable h volume ∧
      ∀ ξ ∈ Metric.ball w r, 𝓕 f ξ * 𝓕 h ξ = 1 := by
    intro w
    obtain ⟨h, r, hr, hh, he⟩ := wtaub_local_inverse hf (hF w)
    refine ⟨h, r, hr, hh, fun ξ hξ => he ξ ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hξ
    exact hξ
  choose hfun rfun hrpos hhint hhe using hloc
  have key : ∀ t : Finset ℝ, ∃ h : ℝ → ℂ, Integrable h volume ∧
      ∀ ξ ∈ ⋃ w ∈ t, Metric.ball w (rfun w), 𝓕 f ξ * 𝓕 h ξ = 1 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨0, integrable_zero _ _ _, fun ξ hξ => ?_⟩
      simp at hξ
    | insert a s has ih =>
      obtain ⟨hprev, hhprev, heprev⟩ := ih
      obtain ⟨h, hh, he⟩ := wtaub_glue hf (hhint a) hhprev (hhe a) heprev
      refine ⟨h, hh, fun ξ hξ => he ξ ?_⟩
      rw [Set.mem_iUnion₂] at hξ
      obtain ⟨w, hwt, hξw⟩ := hξ
      rw [Finset.mem_insert] at hwt
      rcases hwt with rfl | hws
      · exact Set.mem_union_left _ hξw
      · exact Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨w, hws, hξw⟩)
  have hcover : ∀ x ∈ Set.Icc (-R) R, (fun w => Metric.ball w (rfun w)) x ∈ nhds x :=
    fun x _ => Metric.ball_mem_nhds x (hrpos x)
  obtain ⟨t, _, hsub⟩ := isCompact_Icc.elim_nhds_subcover _ hcover
  obtain ⟨h, hh, he⟩ := key t
  exact ⟨h, hh, fun ξ hξ => he ξ (hsub hξ)⟩

-- Reproducing identity.
private theorem wtaub_repro {f h k : ℝ → ℂ} (hf : Integrable f volume)
    (hh : Integrable h volume) (hk : Integrable k volume) {R : ℝ}
    (h1h : ∀ ξ ∈ Set.Icc (-R) R, 𝓕 f ξ * 𝓕 h ξ = 1)
    (hsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-R) R → 𝓕 k ξ = 0) :
    k =ᵐ[volume] ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) := by
  have hkh : Integrable (k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) volume :=
    wtaub_conv_integrable hk hh
  have hq : Integrable
      ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f)
      volume :=
    wtaub_conv_integrable hkh hf
  have hFq : ∀ ξ : ℝ,
      𝓕 ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ =
        𝓕 k ξ := by
    intro ξ
    have e12 : 𝓕 ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ =
        (𝓕 k ξ * 𝓕 h ξ) * 𝓕 f ξ := by
      rw [Real.fourier_mul_convolution_eq hkh hf,
        Real.fourier_mul_convolution_eq hk hh]
    by_cases hξ : ξ ∈ Set.Icc (-R) R
    · have e := h1h ξ hξ
      have e' : 𝓕 h ξ * 𝓕 f ξ = 1 := by
        rw [mul_comm]
        exact e
      calc 𝓕 ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ
            = (𝓕 k ξ * 𝓕 h ξ) * 𝓕 f ξ := e12
          _ = 𝓕 k ξ * (𝓕 h ξ * 𝓕 f ξ) := by ring
          _ = 𝓕 k ξ := by rw [e', mul_one]
    · have e := hsupp ξ hξ
      calc 𝓕 ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ
            = (𝓕 k ξ * 𝓕 h ξ) * 𝓕 f ξ := e12
          _ = 𝓕 k ξ := by rw [e, zero_mul, zero_mul]
  have hkmq : Integrable
      (k - ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f))
      volume :=
    hk.sub hq
  have h0 : ∀ ξ : ℝ,
      𝓕 (k - ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f)) ξ =
        0 := by
    intro ξ
    have e1 : 𝓕 (k - ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f)) ξ =
        𝓕 k ξ -
          𝓕 ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ :=
      wtaub_fourier_sub hk hq ξ
    rw [e1, hFq ξ, sub_self]
  have hae := wtaub_ae_zero hkmq h0
  filter_upwards [hae] with x hx
  have hx' : k x -
      ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] h) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x = 0 :=
    hx
  exact sub_eq_zero.mp hx'

-- Kernel replacement.
private theorem wtaub_kernel_replace {K K' g : ℝ → ℂ} (hK : Integrable K volume)
    (hK' : Integrable K' volume) (hg : Integrable g volume) :
    ∫ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ ≤
      (∫ x, ‖K x - K' x‖) * (∫ x, ‖g x‖) := by
  have hKmK : Integrable (fun x => K x - K' x) volume := hK.sub hK'
  have ae : (fun x => (K ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x) =ᵐ[volume]
      (((fun x => K x - K' x) ⋆[ContinuousLinearMap.mul ℂ ℂ] g)) := by
    filter_upwards [hK'.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ) hg,
      hKmK.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ) hg] with x h1 h2
    have hKeq : (K' + (fun x => K x - K' x)) = K := by
      ext y
      simp only [Pi.add_apply]
      abel
    have h3 : ((K' + (fun x => K x - K' x)) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x =
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x +
          (((fun x => K x - K' x) ⋆[ContinuousLinearMap.mul ℂ ℂ] g)) x :=
      h1.add_distrib h2
    rw [hKeq] at h3
    rw [h3, add_sub_cancel_left]
  calc ∫ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
          (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖
        = ∫ x, ‖(((fun x => K x - K' x) ⋆[ContinuousLinearMap.mul ℂ ℂ] g)) x‖ :=
          integral_congr_ae (ae.mono fun x hx => congrArg _ hx)
      _ ≤ (∫ x, ‖K x - K' x‖) * (∫ x, ‖g x‖) :=
          wtaub_conv_norm_le hKmK hg

-- Helper: support radius and uniform bound for a continuous compactly supported
-- function.
private theorem wtaub_csupp_data {K' : ℝ → ℂ} (hcont : Continuous K')
    (hsupp : HasCompactSupport K') :
    ∃ M : ℝ, 0 < M ∧ (∀ x : ℝ, x ∉ Set.Icc (-M) M → K' x = 0) ∧
      ∃ C : ℝ, ∀ x : ℝ, ‖K' x‖ ≤ C := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport K' ⊆ Metric.closedBall 0 R := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
      hsupp.isCompact.isBounded
    exact ⟨|C| + 1, hC.trans (fun x hx => Metric.mem_closedBall.mpr
      ((Metric.mem_closedBall.mp hx).trans
        ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))))⟩
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
    (hsupp.isCompact.image hcont).isBounded
  refine ⟨|R| + 1, by positivity, ?_, |C| + 1, ?_⟩
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    have hxR : ‖x‖ ≤ R := by
      have hmem' : x ∈ Metric.closedBall 0 R := hR hmem
      have hle' : dist x 0 ≤ R := Metric.mem_closedBall.mp hmem'
      rwa [dist_zero_right] at hle'
    have hM : |x| ≤ |R| + 1 := by
      rw [← Real.norm_eq_abs]
      exact hxR.trans ((le_abs_self R).trans (le_add_of_nonneg_right zero_le_one))
    rw [Set.mem_Icc]
    exact abs_le.mp hM
  · intro y
    by_cases hy : y ∈ tsupport K'
    · have h1 : dist (K' y) 0 ≤ C :=
        Metric.mem_closedBall.mp (hC ⟨y, hy, rfl⟩)
      calc ‖K' y‖ = dist (K' y) 0 := (dist_zero_right _).symm
        _ ≤ |C| + 1 :=
          h1.trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      positivity

-- Helper: per-piece L¹ estimate over one set `s`.
private theorem wtaub_piece_le {K' g : ℝ → ℂ} (hK' : Integrable K' volume)
    (hg : Integrable g volume) (a : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {E : ℝ} (hE : ∀ t ∈ s, ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume ≤ E) :
    Integrable (fun x => ∫ t in s, K' t * (g (x - t) - g (x - a))) volume ∧
    ∫ x, ‖∫ t in s, K' t * (g (x - t) - g (x - a))‖ ≤
      E * ∫ t in s, ‖K' t‖ := by
  have hshift_eq : ∀ t : ℝ, (∫ x, ‖g (x - t) - g (x - a)‖ ∂volume) =
      ∫ y, ‖g (y - (t - a)) - g y‖ ∂volume := by
    intro t
    have h := integral_sub_right_eq_self (μ := volume)
      (fun y => ‖g (y - (t - a)) - g y‖) a
    rw [← h]
    congr 1
    ext x
    change ‖g (x - t) - g (x - a)‖ = ‖g ((x - a) - (t - a)) - g (x - a)‖
    have e : (x - a) - (t - a) = x - t := by ring
    rw [e]
  have hmeas_vol : AEStronglyMeasurable (fun p : ℝ × ℝ => g (p.1 - p.2))
      (volume.prod volume) := by
    have hmap : AEStronglyMeasurable g
        (Measure.map (fun p : ℝ × ℝ => p.1 - p.2) (volume.prod volume)) :=
      hg.aestronglyMeasurable.mono_ac
        (quasiMeasurePreserving_sub_of_right_invariant volume volume).absolutelyContinuous
    exact hmap.comp_measurable measurable_sub
  have hmeas_sub : AEStronglyMeasurable (fun p : ℝ × ℝ => g (p.1 - p.2))
      (volume.prod (volume.restrict s)) := by
    have h0 := hmeas_vol.restrict (s := Set.univ ×ˢ s)
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h0
    exact h0
  have hKt : AEStronglyMeasurable (fun p : ℝ × ℝ => K' p.2)
      (volume.prod (volume.restrict s)) :=
    (hK'.aestronglyMeasurable.restrict (s := s)).comp_snd
  have hGa : AEStronglyMeasurable (fun p : ℝ × ℝ => g (p.1 - a))
      (volume.prod (volume.restrict s)) :=
    ((hg.comp_sub_right a).aestronglyMeasurable).comp_fst
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => K' p.2 * (g (p.1 - p.2) - g (p.1 - a)))
      (volume.prod (volume.restrict s)) :=
    hKt.mul (hmeas_sub.sub hGa)
  have hGmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ‖K' p.2‖ * ‖g (p.1 - p.2) - g (p.1 - a)‖)
      (volume.prod (volume.restrict s)) :=
    hKt.norm.mul (hmeas_sub.sub hGa).norm
  have hsliceG : ∀ t : ℝ, Integrable
      (fun x => ‖K' t‖ * ‖g (x - t) - g (x - a)‖) volume :=
    fun t => (((hg.comp_sub_right t).sub (hg.comp_sub_right a)).norm).const_mul _
  have hnormB : ∀ x t : ℝ,
      ‖(fun p : ℝ × ℝ => ‖K' p.2‖ * ‖g (p.1 - p.2) - g (p.1 - a)‖) (x, t)‖ =
      ‖K' t‖ * ‖g (x - t) - g (x - a)‖ := by
    intro x t
    have hnn : 0 ≤ (fun p : ℝ × ℝ => ‖K' p.2‖ *
        ‖g (p.1 - p.2) - g (p.1 - a)‖) (x, t) := by
      change 0 ≤ ‖K' t‖ * ‖g (x - t) - g (x - a)‖
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hωmeas0 : AEStronglyMeasurable
      (fun t => ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume) (volume.restrict s) := by
    have e : (fun t => ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume) =
        (fun τ => ∫ x, ‖g (x - τ) - g x‖ ∂volume) ∘ fun t => t - a :=
      funext fun t => hshift_eq t
    rw [e]
    exact ((wtaub_translate_continuous hg).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.restrict
  have hωmeas : AEStronglyMeasurable
      (fun t => ‖K' t‖ * ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume)
      (volume.restrict s) :=
    (hK'.norm.aestronglyMeasurable.restrict).mul hωmeas0
  have hbound : ∀ᵐ t ∂(volume.restrict s),
      ‖∫ x, ‖K' t‖ * ‖g (x - t) - g (x - a)‖ ∂volume‖ ≤ ‖K' t‖ * E := by
    filter_upwards [ae_restrict_mem hs] with t ht
    have e : (∫ x, ‖K' t‖ * ‖g (x - t) - g (x - a)‖ ∂volume) =
        ‖K' t‖ * ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume :=
      integral_const_mul _ _
    rw [e, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
      (integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (hE t ht) (norm_nonneg _)
  have hωmeasG : AEStronglyMeasurable
      (fun t => ∫ x, ‖K' t‖ * ‖g (x - t) - g (x - a)‖ ∂volume)
      (volume.restrict s) := by
    have e : (fun t => ∫ x, ‖K' t‖ * ‖g (x - t) - g (x - a)‖ ∂volume) =
        (fun t => ‖K' t‖ * ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume) := by
      funext t
      exact integral_const_mul _ _
    rw [e]
    exact hωmeas
  have hBout : Integrable
      (fun t => ∫ x, ‖K' t‖ * ‖g (x - t) - g (x - a)‖ ∂volume)
      (volume.restrict s) :=
    ((hK'.norm.restrict).mul_const E).mono' hωmeasG hbound
  have hBout2 : Integrable
      (fun t => ‖K' t‖ * ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume)
      (volume.restrict s) := by
    have e : (fun t => ‖K' t‖ * ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume) =
        (fun t => ∫ x, ‖K' t‖ * ‖g (x - t) - g (x - a)‖ ∂volume) := by
      funext t
      exact (integral_const_mul _ _).symm
    rw [e]
    exact hBout
  have hGprod : Integrable
      (fun p : ℝ × ℝ => ‖K' p.2‖ * ‖g (p.1 - p.2) - g (p.1 - a)‖)
      (volume.prod (volume.restrict s)) := by
    rw [integrable_prod_iff' hGmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards with t
      exact hsliceG t
    · have e : (fun t => ∫ x, ‖(fun p : ℝ × ℝ => ‖K' p.2‖ *
          ‖g (p.1 - p.2) - g (p.1 - a)‖) (x, t)‖ ∂volume) =
          (fun t => ∫ x, ‖K' t‖ * ‖g (x - t) - g (x - a)‖ ∂volume) := by
        funext t
        exact integral_congr_ae (ae_of_all _ fun x => hnormB x t)
      rw [e]
      exact hBout
  have hFprod : Integrable
      (fun p : ℝ × ℝ => K' p.2 * (g (p.1 - p.2) - g (p.1 - a)))
      (volume.prod (volume.restrict s)) :=
    hGprod.mono' hFmeas (ae_of_all _ fun p => le_of_eq (norm_mul _ _))
  have hN : Integrable
      (fun x => ∫ t, ‖(fun p : ℝ × ℝ => K' p.2 *
        (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖ ∂(volume.restrict s)) volume :=
    hFprod.integral_norm_prod_left
  have hPmeas : AEStronglyMeasurable
      (fun x => ∫ t, (fun p : ℝ × ℝ => K' p.2 *
        (g (p.1 - p.2) - g (p.1 - a))) (x, t) ∂(volume.restrict s)) volume :=
    hFmeas.integral_prod_right'
  have hP : Integrable (fun x => ∫ t in s, K' t * (g (x - t) - g (x - a))) volume :=
    hN.mono' hPmeas (ae_of_all _ fun x => norm_integral_le_integral_norm _)
  have hnormF : ∀ x t : ℝ,
      ‖(fun p : ℝ × ℝ => K' p.2 * (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖ =
      ‖K' t‖ * ‖g (x - t) - g (x - a)‖ :=
    fun x t => norm_mul _ _
  have hinner : ∀ t : ℝ,
      (∫ x, ‖(fun p : ℝ × ℝ => K' p.2 * (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖
        ∂volume) =
      ‖K' t‖ * ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume := by
    intro t
    exact (integral_congr_ae
      (ae_of_all _ fun x => hnormF x t)).trans (integral_const_mul _ _)
  have hswap : (∫ x, ∫ t, ‖(fun p : ℝ × ℝ => K' p.2 *
        (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖ ∂(volume.restrict s) ∂volume) =
      (∫ t, ∫ x, ‖(fun p : ℝ × ℝ => K' p.2 *
        (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖ ∂volume ∂(volume.restrict s)) := by
    have hU : Integrable
        (Function.uncurry fun x t => ‖(fun p : ℝ × ℝ => K' p.2 *
          (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖)
        (volume.prod (volume.restrict s)) := hFprod.norm
    exact MeasureTheory.integral_integral_swap hU
  refine ⟨hP, ?_⟩
  calc ∫ x, ‖∫ t in s, K' t * (g (x - t) - g (x - a))‖
        ≤ ∫ x, ∫ t, ‖(fun p : ℝ × ℝ => K' p.2 *
            (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖ ∂(volume.restrict s) ∂volume :=
          integral_mono hP.norm hN (fun x => norm_integral_le_integral_norm _)
      _ = ∫ t, ∫ x, ‖(fun p : ℝ × ℝ => K' p.2 *
            (g (p.1 - p.2) - g (p.1 - a))) (x, t)‖ ∂volume
          ∂(volume.restrict s) := hswap
      _ = ∫ t, ‖K' t‖ * ∫ x, ‖g (x - t) - g (x - a)‖ ∂volume
          ∂(volume.restrict s) := by
          apply integral_congr_ae
          filter_upwards with t
          exact hinner t
      _ ≤ ∫ t, ‖K' t‖ * E ∂(volume.restrict s) := by
          apply integral_mono_ae hBout2 ((hK'.norm.restrict).mul_const E)
          filter_upwards [ae_restrict_mem hs] with t ht
          exact mul_le_mul_of_nonneg_left (hE t ht) (norm_nonneg _)
      _ = E * ∫ t in s, ‖K' t‖ := by
          rw [integral_mul_const, mul_comm]

-- Riemann sums of translates.
private theorem wtaub_riemann {K' g : ℝ → ℂ} (hK'c : Continuous K')
    (hK's : HasCompactSupport K') (hg : Integrable g volume) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s : Finset ℝ, ∃ c : ℝ → ℂ,
      ∫ x, ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
        ∑ t ∈ s, c t * g (x - t)‖ < ε := by
  obtain ⟨M, hMpos, hsupp0, C, hC⟩ := wtaub_csupp_data hK'c hK's
  have hK'int : Integrable K' volume := hK'c.integrable_of_hasCompactSupport hK's
  have hnnK : 0 ≤ ∫ x, ‖K' x‖ :=
    integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
  have hApos : 0 < 1 + ∫ x, ‖K' x‖ := by linarith
  obtain ⟨η₀, hη₀pos, hη₀⟩ := Metric.eventually_nhds_iff.mp
    ((Metric.tendsto_nhds.mp (wtaub_translate_tendsto hg)) _
      (div_pos hε hApos))
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M / η₀)
  have hNcast : (0 : ℝ) < N := by
    have hle : (0 : ℝ) ≤ 2 * M / η₀ :=
      div_nonneg (by linarith) hη₀pos.le
    have hlt : (0 : ℝ) < N := lt_of_le_of_lt hle hN
    exact_mod_cast Nat.cast_pos.mp hlt
  set η : ℝ := 2 * M / N with hηdef
  have hηnn : 0 ≤ η := by
    rw [hηdef]
    exact div_nonneg (by linarith) hNcast.le
  have hηlt : η < η₀ := by
    have h := (div_lt_iff₀ hη₀pos).mp hN
    rw [hηdef, div_lt_iff₀ hNcast]
    linarith [h]
  have hηpos : 0 < η := by
    rw [hηdef]
    exact div_pos (by linarith) hNcast
  have hηne : η ≠ 0 := ne_of_gt hηpos
  set t : ℕ → ℝ := fun j => -M + j * η with htdef
  have ht0 : t 0 = -M := by simp [htdef]
  have hNη : (N : ℝ) * η = 2 * M := by
    rw [hηdef, mul_comm, div_mul_cancel₀ _ (ne_of_gt hNcast)]
  have htN : t N = M := by
    simp only [htdef]
    linarith [hNη]
  have htsucc : ∀ j : ℕ, t (j + 1) = t j + η := by
    intro j
    simp only [htdef]
    push_cast
    ring
  have htinj : Function.Injective t := by
    intro j₁ j₂ h
    simp only [htdef] at h
    have h1 : (j₁ : ℝ) * η = (j₂ : ℝ) * η := add_left_cancel_iff.mp h
    have h2 : (j₁ : ℝ) = j₂ := mul_right_cancel₀ hηne h1
    exact Nat.cast_injective h2
  set s : Finset ℝ := (Finset.range N).image t with hsdef
  set c : ℝ → ℂ := fun u => ∫ v in Set.Ioc u (u + η), K' v ∂volume with hcdef
  have hE : ∀ j : ℕ, ∀ τ ∈ Set.Ioc (t j) (t j + η),
      ∫ x, ‖g (x - τ) - g (x - t j)‖ ∂volume ≤ ε / (1 + ∫ x, ‖K' x‖) := by
    intro j τ hτ
    have hsh : (∫ x, ‖g (x - τ) - g (x - t j)‖ ∂volume) =
        ∫ y, ‖g (y - (τ - t j)) - g y‖ ∂volume := by
      have h := integral_sub_right_eq_self (μ := volume)
        (fun y => ‖g (y - (τ - t j)) - g y‖) (t j)
      rw [← h]
      congr 1
      ext x
      change ‖g (x - τ) - g (x - t j)‖ = ‖g ((x - t j) - (τ - t j)) - g (x - t j)‖
      have e : (x - t j) - (τ - t j) = x - τ := by ring
      rw [e]
    rw [hsh]
    have hb : 0 ≤ τ - t j ∧ τ - t j ≤ η := by
      obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp hτ
      constructor <;> linarith
    have hdist : dist (τ - t j) 0 < η₀ := by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact lt_of_le_of_lt hb.2 hηlt
    have hΦ := hη₀ hdist
    rw [dist_zero_right, Real.norm_of_nonneg (integral_nonneg_of_ae
      (ae_of_all _ fun x => norm_nonneg _))] at hΦ
    exact le_of_lt hΦ
  have hpiece : ∀ j : ℕ, Integrable
      (fun x => ∫ v in Set.Ioc (t j) (t j + η), K' v * (g (x - v) - g (x - t j)))
      volume ∧
      (∫ x, ‖∫ v in Set.Ioc (t j) (t j + η), K' v * (g (x - v) - g (x - t j))‖) ≤
        (ε / (1 + ∫ x, ‖K' x‖)) *
          ∫ v in Set.Ioc (t j) (t j + η), ‖K' v‖ :=
    fun j => wtaub_piece_le hK'int hg (t j) measurableSet_Ioc (hE j)
  have hconvx : ∀ x : ℝ, (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x =
      ∫ v, K' v * g (x - v) ∂volume := by
    intro x
    rw [MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with v
    exact ContinuousLinearMap.mul_apply' _ _ _ _
  have hsuppx : ∀ x : ℝ, (∫ v, K' v * g (x - v) ∂volume) =
      ∫ v in Set.Icc (-M) M, K' v * g (x - v) ∂volume := by
    intro x
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hsupp0 v hv, zero_mul]
  have hFx : ∀ x : ℝ, Integrable (fun v => K' v * g (x - v)) volume := by
    intro x
    have hshift : Integrable (fun v => g (x - v)) volume := by
      have h1 := (hg.comp_add_left x).comp_neg
      have e : (fun v => g (x - v)) = (fun v => g (x + -v)) := by
        funext v
        rw [sub_eq_add_neg]
      rw [e]
      exact h1
    exact hshift.bdd_mul hK'c.aestronglyMeasurable (ae_of_all _ fun v => hC v)
  have htile : ∀ x : ℝ,
      (∫ v in Set.Icc (-M) M, K' v * g (x - v) ∂volume) =
      ∑ j ∈ Finset.range N,
        ∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - v) ∂volume := by
    intro x
    have hinterv : ∀ k < N,
        IntervalIntegrable (fun v => K' v * g (x - v)) volume (t k) (t (k + 1)) :=
      fun k _ => (hFx x).intervalIntegrable
    have hadj := intervalIntegral.sum_integral_adjacent_intervals hinterv
    have hpiece_eq : ∀ j : ℕ,
        (∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - v) ∂volume) =
        ∫ v in t j..t (j + 1), K' v * g (x - v) ∂volume := by
      intro j
      rw [htsucc j]
      exact (intervalIntegral.integral_of_le
        (show t j ≤ t j + η by linarith)).symm
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -M ≤ M by linarith),
      ← ht0, ← htN, ← hadj]
    exact Finset.sum_congr rfl (fun j _ => (hpiece_eq j).symm)
  have hsum : ∀ x : ℝ, (∑ u ∈ s, c u * g (x - u)) =
      ∑ j ∈ Finset.range N,
        (∫ v in Set.Ioc (t j) (t j + η), K' v ∂volume) * g (x - t j) := by
    intro x
    rw [hsdef, Finset.sum_image htinj.injOn]
  have hdiff : ∀ x : ℝ, (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
      ∑ u ∈ s, c u * g (x - u) =
      ∑ j ∈ Finset.range N, (∫ v in Set.Ioc (t j) (t j + η),
        K' v * (g (x - v) - g (x - t j)) ∂volume) := by
    intro x
    rw [hconvx x, hsuppx x, htile x, hsum x, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : Integrable (fun v => K' v * g (x - v))
        (volume.restrict (Set.Ioc (t j) (t j + η))) :=
      (hFx x).restrict
    have h2 : Integrable (fun v => K' v * g (x - t j))
        (volume.restrict (Set.Ioc (t j) (t j + η))) :=
      (hK'int.restrict).mul_const _
    have hmul : (∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - t j) ∂volume) =
        (∫ v in Set.Ioc (t j) (t j + η), K' v ∂volume) * g (x - t j) :=
      integral_mul_const _ _
    have hsub : (∫ v in Set.Ioc (t j) (t j + η),
          (K' v * g (x - v) - K' v * g (x - t j)) ∂volume) =
        (∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - v) ∂volume) -
        ∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - t j) ∂volume :=
      integral_sub h1 h2
    have hpt : ∀ v : ℝ, K' v * g (x - v) - K' v * g (x - t j) =
        K' v * (g (x - v) - g (x - t j)) :=
      fun v => (mul_sub _ _ _).symm
    calc (∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - v) ∂volume) -
            ((∫ v in Set.Ioc (t j) (t j + η), K' v ∂volume) * g (x - t j))
        = (∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - v) ∂volume) -
            ∫ v in Set.Ioc (t j) (t j + η), K' v * g (x - t j) ∂volume := by
          rw [hmul]
      _ = ∫ v in Set.Ioc (t j) (t j + η),
            K' v * (g (x - v) - g (x - t j)) ∂volume := by
          rw [← hsub]
          exact integral_congr_ae (ae_of_all _ hpt)
  have htileK : (∑ j ∈ Finset.range N,
      ∫ v in Set.Ioc (t j) (t j + η), ‖K' v‖ ∂volume) =
      ∫ v in Set.Icc (-M) M, ‖K' v‖ ∂volume := by
    have hintervK : ∀ k < N,
        IntervalIntegrable (fun v => ‖K' v‖) volume (t k) (t (k + 1)) :=
      fun k _ => hK'int.norm.intervalIntegrable
    have hadjK := intervalIntegral.sum_integral_adjacent_intervals hintervK
    have hpieceK : ∀ j : ℕ, (∫ v in Set.Ioc (t j) (t j + η), ‖K' v‖ ∂volume) =
        ∫ v in t j..t (j + 1), ‖K' v‖ ∂volume := by
      intro j
      rw [htsucc j]
      exact (intervalIntegral.integral_of_le
        (show t j ≤ t j + η by linarith)).symm
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -M ≤ M by linarith),
      ← ht0, ← htN, ← hadjK]
    exact Finset.sum_congr rfl (fun j _ => hpieceK j)
  refine ⟨s, c, ?_⟩
  calc (∫ x, ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - ∑ u ∈ s, c u * g (x - u)‖)
      = ∫ x, ‖∑ j ∈ Finset.range N, ∫ v in Set.Ioc (t j) (t j + η),
          K' v * (g (x - v) - g (x - t j)) ∂volume‖ := by simp only [hdiff]
    _ ≤ ∫ x, ∑ j ∈ Finset.range N, ‖∫ v in Set.Ioc (t j) (t j + η),
          K' v * (g (x - v) - g (x - t j))‖ := by
        have hPsum : Integrable
            (fun x => ∑ j ∈ Finset.range N, ∫ v in Set.Ioc (t j) (t j + η),
              K' v * (g (x - v) - g (x - t j))) volume :=
          integrable_finsetSum _ (fun j _ => (hpiece j).1)
        exact integral_mono hPsum.norm
          (integrable_finsetSum _ (fun j _ => ((hpiece j).1).norm))
          (fun x => norm_sum_le _ _)
    _ = ∑ j ∈ Finset.range N, ∫ x, ‖∫ v in Set.Ioc (t j) (t j + η),
          K' v * (g (x - v) - g (x - t j))‖ :=
        integral_finsetSum _ (fun j _ => ((hpiece j).1).norm)
    _ ≤ ∑ j ∈ Finset.range N, (ε / (1 + ∫ x, ‖K' x‖)) *
          ∫ v in Set.Ioc (t j) (t j + η), ‖K' v‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (hpiece j).2
    _ = (ε / (1 + ∫ x, ‖K' x‖)) *
          ∑ j ∈ Finset.range N,
            ∫ v in Set.Ioc (t j) (t j + η), ‖K' v‖ := by
        rw [Finset.mul_sum]
    _ = (ε / (1 + ∫ x, ‖K' x‖)) * ∫ v in Set.Icc (-M) M, ‖K' v‖ ∂volume := by
        rw [htileK]
    _ ≤ (ε / (1 + ∫ x, ‖K' x‖)) * ∫ v, ‖K' v‖ ∂volume := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hε.le hApos.le)
        exact setIntegral_le_integral hK'int.norm
          (ae_of_all _ fun v => norm_nonneg _)
    _ < ε := by
        have hlt : (∫ v, ‖K' v‖ ∂volume) < 1 + ∫ x, ‖K' x‖ := by linarith
        calc (ε / (1 + ∫ x, ‖K' x‖)) * ∫ v, ‖K' v‖ ∂volume
            < (ε / (1 + ∫ x, ‖K' x‖)) * (1 + ∫ x, ‖K' x‖) :=
              mul_lt_mul_of_pos_left hlt (div_pos hε hApos)
          _ = ε := div_mul_cancel₀ _ (ne_of_gt hApos)

end MathlibExt.Analysis.Fourier.WienerWanted

@[expose] public section

open MeasureTheory Complex
open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.WienerWanted

/--
**Wiener's Tauberian theorem on $L^1(\mathbb{R})$.** Let $f : \mathbb{R} \to \mathbb{C}$ be
Lebesgue integrable, and suppose that its Fourier transform
$\hat f(w) = \int_{\mathbb{R}} e^{-2\pi i x w} f(x)\,dx$ vanishes at no real $w$. Then for every
Lebesgue integrable $g : \mathbb{R} \to \mathbb{C}$ and every $\varepsilon > 0$ there are a finite
set $S \subset \mathbb{R}$ and coefficients $c_t \in \mathbb{C}$ for $t \in S$ such that the
function $h(x) = g(x) - \sum_{t \in S} c_t f(x - t)$ is integrable and
$\int_{\mathbb{R}} |h(x)|\,dx < \varepsilon$. In other words, the translates of $f$ span a dense
subspace of $L^1(\mathbb{R})$.

Proves `Wanted` entry `wiener_tauberian_L1`.

Source: N. Wiener, Ann. of Math. 33 (1932) 1–100, DOI 10.2307/1968102, Thm I; Rudin, Fourier
Analysis on Groups
-/
theorem wiener_tauberian_L1
    (f : ℝ → ℂ) (hf : Integrable f volume)
    (hF : ∀ w : ℝ, 𝓕 f w ≠ 0) :
    ∀ (g : ℝ → ℂ), Integrable g volume → ∀ ε > 0,
      ∃ (s : Finset ℝ) (c : ℝ → ℂ),
        Integrable (fun x => g x - ∑ t ∈ s, c t * f (x - t)) volume ∧
        ∫ x, ‖g x - ∑ t ∈ s, c t * f (x - t)‖ < ε := by
  intro g hg ε hε
  obtain ⟨V, _, hVi, _, _, hV0, hVint1⟩ := wtaub_bump
  obtain ⟨lam, hlampos, hlam⟩ := wtaub_approx_id_small hVi hg hVint1
    (show (0 : ℝ) < ε / 3 by linarith)
  have hWdil : Integrable (wtaubDil V lam) volume :=
    (hVi.comp_mul_left' (ne_of_gt hlampos)).const_mul _
  have hk : Integrable (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) volume :=
    wtaub_conv_integrable hWdil hg
  have hWdileq : wtaubModDil V 0 lam = wtaubDil V lam := by
    funext x
    simp only [wtaubModDil, wtaubDil, zero_mul,
      Real.fourierChar.map_zero_eq_one, Circle.coe_one, one_mul]
  have hWfourier : ∀ ξ : ℝ, 𝓕 (wtaubDil V lam) ξ = 𝓕 V (ξ / lam) := by
    intro ξ
    rw [← hWdileq, wtaub_modDil_fourier hVi 0 hlampos ξ, sub_zero]
  have hksupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(2 * lam)) (2 * lam) →
      𝓕 (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ = 0 := by
    intro ξ hξ
    have h2 : 2 * lam < |ξ| := by
      rw [Set.mem_Icc, not_and_or] at hξ
      rcases hξ with h | h
      · rw [not_le] at h
        rw [abs_of_neg (by linarith : ξ < 0)]
        linarith
      · rw [not_le] at h
        rw [abs_of_pos (by linarith : 0 < ξ)]
        exact h
    have hV0' : 𝓕 V (ξ / lam) = 0 := by
      apply hV0
      rw [abs_div, abs_of_pos hlampos, le_div_iff₀ hlampos]
      linarith [h2]
    rw [Real.fourier_mul_convolution_eq hWdil hg ξ, hWfourier ξ, hV0', zero_mul]
  obtain ⟨h, hh, h1h⟩ := wtaub_inverse_on_Icc hf hF (2 * lam)
  set K : ℝ → ℂ := ((wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g)
    ⋆[ContinuousLinearMap.mul ℂ ℂ] h) with hKdef
  have hkh : Integrable K volume :=
    wtaub_conv_integrable (wtaub_conv_integrable hWdil hg) hh
  have hrepro : (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) =ᵐ[volume]
      (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) :=
    wtaub_repro hf hh (wtaub_conv_integrable hWdil hg) h1h hksupp
  have hnnf : 0 ≤ ∫ x, ‖f x‖ :=
    integral_nonneg_of_ae (ae_of_all _ fun x => norm_nonneg _)
  have hAposf : 0 < 1 + ∫ x, ‖f x‖ := by linarith
  obtain ⟨K', hKs, hKclose, hKc, hKint⟩ :=
    hkh.exists_hasCompactSupport_integral_sub_le
      (div_pos hε (by linarith [hAposf] : 0 < 3 * (1 + ∫ x, ‖f x‖)))
  have e : ε / (3 * (1 + ∫ x, ‖f x‖)) * (1 + ∫ x, ‖f x‖) = ε / 3 := by
    have e0 : ε / (3 * (1 + ∫ x, ‖f x‖)) = ε / 3 / (1 + ∫ x, ‖f x‖) := by
      rw [div_div]
    rw [e0]
    exact div_mul_cancel₀ _ (ne_of_gt hAposf)
  have hrep : (∫ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
      (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) < ε / 3 := by
    have hle := wtaub_kernel_replace hkh hKint hf
    have hstep : (∫ x, ‖K x - K' x‖) * (∫ x, ‖f x‖) < ε / 3 := by
      calc (∫ x, ‖K x - K' x‖) * (∫ x, ‖f x‖)
          ≤ (ε / (3 * (1 + ∫ x, ‖f x‖))) * (∫ x, ‖f x‖) :=
            mul_le_mul_of_nonneg_right hKclose hnnf
        _ < ε / 3 := by
            have hlt : (∫ x, ‖f x‖) < 1 + ∫ x, ‖f x‖ := by linarith [hAposf]
            calc (ε / (3 * (1 + ∫ x, ‖f x‖))) * (∫ x, ‖f x‖)
                < (ε / (3 * (1 + ∫ x, ‖f x‖))) * (1 + ∫ x, ‖f x‖) :=
                  mul_lt_mul_of_pos_left hlt (div_pos hε (by linarith [hAposf]))
              _ = ε / 3 := e
    exact lt_of_le_of_lt hle hstep
  obtain ⟨s, c, hN15⟩ := wtaub_riemann hKc hKs hf
    (show (0 : ℝ) < ε / 3 by linarith)
  have hS : Integrable (fun x => ∑ t ∈ s, c t * f (x - t)) volume :=
    integrable_finsetSum _ (fun u _ => (hf.comp_sub_right u).const_mul _)
  have hInt : Integrable (fun x => g x - ∑ t ∈ s, c t * f (x - t)) volume :=
    hg.sub hS
  have hKf : Integrable (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) volume :=
    wtaub_conv_integrable hkh hf
  have hK'f : Integrable (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) volume :=
    wtaub_conv_integrable hKint hf
  have h1 : Integrable
      (fun x => ‖g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖)
      volume :=
    (hg.sub hk).norm
  have h2 : Integrable
      (fun x => ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
        (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) volume :=
    (hk.sub hKf).norm
  have h3 : Integrable
      (fun x => ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) volume :=
    (hKf.sub hK'f).norm
  have h4 : Integrable
      (fun x => ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        ∑ t ∈ s, c t * f (x - t)‖) volume :=
    (hK'f.sub hS).norm
  have hlam' : (∫ x, ‖g x -
      (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) < ε / 3 :=
    lt_of_eq_of_lt
      (integral_congr_ae (ae_of_all _ fun x => norm_sub_rev _ _)) hlam
  have hzero : (∫ x, ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
      (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) = 0 := by
    have hae : (fun x => ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
        (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) =ᵐ[volume] fun _ => (0 : ℝ) := by
      filter_upwards [hrepro] with x hx
      rw [hx, sub_self, norm_zero]
    rw [integral_congr_ae hae, integral_zero]
  have hpt : ∀ x : ℝ, ‖g x - ∑ t ∈ s, c t * f (x - t)‖ ≤
      (‖g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ +
        ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
          (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) +
      (‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ +
        ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖) := by
    intro x
    have e : g x - ∑ t ∈ s, c t * f (x - t) =
        ((g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x) +
          ((wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
            (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x)) +
        (((K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x) +
          ((K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
            ∑ t ∈ s, c t * f (x - t))) := by
      abel
    rw [e]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) (norm_add_le _ _))
  have hRHS : Integrable (fun x => (‖g x -
      (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ +
        ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
          (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) +
      (‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ +
        ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖)) volume :=
    (h1.add h2).add (h3.add h4)
  have hmono : (∫ x, ‖g x - ∑ t ∈ s, c t * f (x - t)‖) ≤
      ∫ x, (‖g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ +
        ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
          (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) +
      (‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ +
        ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖) :=
    integral_mono hInt.norm hRHS hpt
  have h12 : Integrable (fun x => ‖g x -
      (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ +
        ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
          (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) volume :=
    h1.add h2
  have h34 : Integrable (fun x => ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
      (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ +
        ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖) volume :=
    h3.add h4
  have e12 : (∫ x, ‖g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ +
      ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
        (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) =
      (∫ x, ‖g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) +
        ∫ x, ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
          (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ :=
    integral_add h1 h2
  have e34 : (∫ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
      (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ +
        ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖) =
      (∫ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) +
        ∫ x, ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖ :=
    integral_add h3 h4
  have e1234 : (∫ x, (‖g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ +
      ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
        (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) +
      (‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ +
        ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖)) =
      (∫ x, ‖g x - (wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ +
        ‖(wtaubDil V lam ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x -
          (K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖) +
      ∫ x, ‖(K ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
        (K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x‖ +
        ‖(K' ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x -
          ∑ t ∈ s, c t * f (x - t)‖ :=
    integral_add h12 h34
  refine ⟨s, c, hInt, ?_⟩
  linarith [hmono, e1234, e12, e34, hlam', hzero, hrep, hN15]

end MathlibExt.Analysis.Fourier.WienerWanted
