/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.DirichletForm
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.DirichletForm

open Set Filter Topology MeasureTheory MathlibExt.Biology.PopulationGenetics.Diffusion
open scoped ENNReal

example :
    ∫ x, x * diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
        (fun x => x ^ 2) x
      ∂(speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) =
      (2 - 0 : ℝ) - ∫ x in (0 : ℝ)..1, deriv (fun x : ℝ => x) x *
        deriv (fun x : ℝ => x ^ 2) x /
        scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x := by
  have hψ : ∀ x, scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 1 := by
    intro x
    simp [scaleDensityFrom]
  have hσ : ∀ x, speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 2 := by
    intro x
    simp only [speedDensityFrom, hψ, mul_one, div_one]
  have hL : ∀ (u : ℝ → ℝ) (x : ℝ), diffusionGenerator (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) u x = deriv (deriv u) x / 2 := by
    intro u x
    simp only [diffusionGenerator]
    ring
  have ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun _ => (1 : ℝ)) x := by
    intro x _
    exact one_pos
  have ha_cont : ContinuousOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const
  have hba_cont : ContinuousOn (fun x : ℝ => (0 : ℝ) / (1 : ℝ))
      (Ioo (0 : ℝ) 1) := by
    simp only [zero_div]
    exact continuousOn_const
  have hc : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x) (Icc (0 : ℝ) 1) := contDiffOn_id
  have hg : ContDiffOn ℝ 2 (fun x : ℝ => x ^ 2) (Icc (0 : ℝ) 1) := by
    have hmul : ContDiffOn ℝ 2 (fun x : ℝ => x * x) (Icc (0 : ℝ) 1) :=
      contDiffOn_id.mul contDiffOn_id
    simpa only [pow_two] using hmul
  have d1 : ∀ y, deriv (fun x : ℝ => x) y = 1 := by
    intro y
    simp
  have d2 : ∀ y, deriv (fun x : ℝ => x ^ 2) y = 2 * y := by
    intro y
    simp
  have dd2 : ∀ y, deriv (deriv (fun x : ℝ => x ^ 2)) y = 2 := by
    intro y
    have hfun : deriv (fun x : ℝ => x ^ 2) = fun y => 2 * y := funext d2
    rw [hfun]
    simp
  have hLg : ∀ y, diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x ^ 2) y = 1 := by
    intro y
    rw [hL, dd2]
    norm_num
  have hB0 : Tendsto (fun y : ℝ => (fun x => x) y * (deriv (fun x => x ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x) y * (deriv (fun x => x ^ 2) y /
        scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => 2 * y ^ 2 := by
      funext y
      rw [d2 y, hψ y, div_one]
      show y * (2 * y) = 2 * y ^ 2
      ring
    rw [hfun]
    have hc0 : ContinuousAt (fun y : ℝ => 2 * y ^ 2) 0 := by fun_prop
    have h0 : (fun y : ℝ => 2 * y ^ 2) 0 = 0 := by norm_num
    have ht : Tendsto (fun y : ℝ => 2 * y ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 ((fun y : ℝ => 2 * y ^ 2) 0)) :=
      hc0.tendsto.mono_left nhdsWithin_le_nhds
    rw [h0] at ht
    exact ht
  have hB1 : Tendsto (fun y : ℝ => (fun x => x) y * (deriv (fun x => x ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y))
      (𝓝[<] (1 : ℝ)) (𝓝 (2 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x) y * (deriv (fun x => x ^ 2) y /
        scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => 2 * y ^ 2 := by
      funext y
      rw [d2 y, hψ y, div_one]
      show y * (2 * y) = 2 * y ^ 2
      ring
    rw [hfun]
    have hc1 : ContinuousAt (fun y : ℝ => 2 * y ^ 2) 1 := by fun_prop
    have h1 : (fun y : ℝ => 2 * y ^ 2) 1 = 2 := by norm_num
    have ht : Tendsto (fun y : ℝ => 2 * y ^ 2) (𝓝[<] (1 : ℝ))
        (𝓝 ((fun y : ℝ => 2 * y ^ 2) 1)) :=
      hc1.tendsto.mono_left nhdsWithin_le_nhds
    rw [h1] at ht
    exact ht
  have hint : Integrable (fun x : ℝ => (fun x => x) x * diffusionGenerator
      (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x => x ^ 2) x)
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    have hfun : (fun x : ℝ => (fun x => x) x * diffusionGenerator (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun x => x ^ 2) x) = fun x => x := by
      funext x
      rw [hLg x]
      simp
    rw [hfun]
    have h_ae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (speedDensityFrom
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x))
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
      simp only [hσ]
      exact aemeasurable_const
    have h_lt : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ENNReal.ofReal
        (speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) < ∞ := by
      simp only [hσ]
      exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    simp only [speedMeasureFrom]
    rw [integrable_withDensity_iff_integrable_smul₀' h_ae h_lt]
    have hsmul : (fun x : ℝ => (ENNReal.ofReal (speedDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) x)).toReal • (fun x' : ℝ => x') x) =
        fun x => 2 * x := by
      funext x
      rw [hσ x, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [smul_eq_mul]
    rw [hsmul]
    have hcont : Continuous (fun x : ℝ => 2 * x) := by fun_prop
    have hIcc : IntegrableOn (fun x : ℝ => 2 * x) (Icc (0 : ℝ) 1) volume :=
      hcont.integrableOn_Icc
    have hIoo := hIcc.mono_set Ioo_subset_Icc_self
    exact hIoo
  have hdir : IntervalIntegrable (fun x : ℝ => deriv (fun x => x) x *
      deriv (fun x => x ^ 2) x / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) x) volume 0 1 := by
    have hfun : (fun x : ℝ => deriv (fun x => x) x * deriv (fun x => x ^ 2) x /
        scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) =
        fun x => 2 * x := by
      funext x
      rw [d1 x, d2 x, hψ x, div_one, one_mul]
    rw [hfun]
    exact (by fun_prop : Continuous (fun x : ℝ => 2 * x)).intervalIntegrable 0 1
  exact integral_mul_diffusionGenerator_speedMeasureFrom (fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ)) (fun x => x) (fun x => x ^ 2) (1 / 2) 0 2 ha ha_cont
    hba_cont hc hf hg hB0 hB1 hint hdir

example :
    ∫ x, (x * (1 - x)) * diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
        (fun x => x ^ 2 * (1 - x)) x
      ∂(speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) =
      ∫ x, (x ^ 2 * (1 - x)) * diffusionGenerator (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun x => x * (1 - x)) x
      ∂(speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
  have hψ : ∀ x, scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 1 := by
    intro x
    simp [scaleDensityFrom]
  have hσ : ∀ x, speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 2 := by
    intro x
    simp only [speedDensityFrom, hψ, mul_one, div_one]
  have hL : ∀ (u : ℝ → ℝ) (x : ℝ), diffusionGenerator (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) u x = deriv (deriv u) x / 2 := by
    intro u x
    simp only [diffusionGenerator]
    ring
  have ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun _ => (1 : ℝ)) x := by
    intro x _
    exact one_pos
  have ha_cont : ContinuousOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const
  have hba_cont : ContinuousOn (fun x : ℝ => (0 : ℝ) / (1 : ℝ))
      (Ioo (0 : ℝ) 1) := by
    simp only [zero_div]
    exact continuousOn_const
  have hc : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x * (1 - x)) (Icc (0 : ℝ) 1) :=
    contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)
  have hg : ContDiffOn ℝ 2 (fun x : ℝ => x ^ 2 * (1 - x)) (Icc (0 : ℝ) 1) := by
    have hmul : ContDiffOn ℝ 2 (fun x : ℝ => x * x) (Icc (0 : ℝ) 1) :=
      contDiffOn_id.mul contDiffOn_id
    have hsq : ContDiffOn ℝ 2 (fun x : ℝ => x ^ 2) (Icc (0 : ℝ) 1) := by
      simpa only [pow_two] using hmul
    have h1x : ContDiffOn ℝ 2 (fun x : ℝ => (1 : ℝ) - x) (Icc (0 : ℝ) 1) :=
      contDiffOn_const.sub contDiffOn_id
    exact hsq.mul h1x
  have df : ∀ y, deriv (fun x : ℝ => x * (1 - x)) y = 1 - 2 * y := by
    intro y
    have h : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 * (1 - y) + y * (0 - 1))
        y :=
      (hasDerivAt_id' (x := y)).mul
        ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub (hasDerivAt_id' (x := y)))
    rw [h.deriv]
    ring
  have dg : ∀ y, deriv (fun x : ℝ => x ^ 2 * (1 - x)) y = 2 * y - 3 * y ^ 2 := by
    intro y
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (((2 : ℕ) : ℝ) * y ^ (2 - 1) * 1)
        y :=
      (hasDerivAt_id' (x := y)).pow 2
    have h : HasDerivAt (fun x : ℝ => x ^ 2 * (1 - x))
        ((((2 : ℕ) : ℝ) * y ^ (2 - 1) * 1) * (1 - y) + y ^ 2 * (0 - 1)) y :=
      hsq.mul ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub
        (hasDerivAt_id' (x := y)))
    rw [h.deriv]
    simp
    ring
  have ddf : ∀ y, deriv (deriv (fun x : ℝ => x * (1 - x))) y = -2 := by
    intro y
    have hfun : deriv (fun x : ℝ => x * (1 - x)) = fun y => 1 - 2 * y :=
      funext df
    rw [hfun]
    simp
  have ddg : ∀ y, deriv (deriv (fun x : ℝ => x ^ 2 * (1 - x))) y = 2 - 6 * y := by
    intro y
    have hfun : deriv (fun x : ℝ => x ^ 2 * (1 - x)) =
        fun y => 2 * y - 3 * y ^ 2 :=
      funext dg
    rw [hfun]
    have h1 : HasDerivAt (fun y : ℝ => 2 * y) (2 * 1) y :=
      (hasDerivAt_id' (x := y)).const_mul 2
    have h2 : HasDerivAt (fun y : ℝ => 3 * y ^ 2)
        (0 * y ^ 2 + 3 * (((2 : ℕ) : ℝ) * y ^ (2 - 1) * 1)) y :=
      (hasDerivAt_const (x := y) (c := (3 : ℝ))).mul
        ((hasDerivAt_id' (x := y)).pow 2)
    have h : HasDerivAt (fun y : ℝ => 2 * y - 3 * y ^ 2)
        ((2 * 1) - (0 * y ^ 2 + 3 * (((2 : ℕ) : ℝ) * y ^ (2 - 1) * 1))) y :=
      h1.sub h2
    rw [h.deriv]
    simp
    ring
  have hLf : ∀ y, diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x * (1 - x)) y = -1 := by
    intro y
    rw [hL, ddf]
    norm_num
  have hLg : ∀ y, diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x ^ 2 * (1 - x)) y = 1 - 3 * y := by
    intro y
    rw [hL, ddg]
    ring
  have hfg0 : Tendsto (fun y : ℝ => (fun x => x * (1 - x)) y *
      (deriv (fun x => x ^ 2 * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x * (1 - x)) y *
        (deriv (fun x => x ^ 2 * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y * (1 - y)) * (2 * y - 3 * y ^ 2) := by
      funext y
      rw [dg y, hψ y, div_one]
    rw [hfun]
    have hc0 : ContinuousAt (fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2))
        0 := by fun_prop
    have h0 : (fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2)) 0 = 0 := by
      norm_num
    have ht : Tendsto (fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2)) 0)) :=
      hc0.tendsto.mono_left nhdsWithin_le_nhds
    rw [h0] at ht
    exact ht
  have hfg1 : Tendsto (fun y : ℝ => (fun x => x * (1 - x)) y *
      (deriv (fun x => x ^ 2 * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x * (1 - x)) y *
        (deriv (fun x => x ^ 2 * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y * (1 - y)) * (2 * y - 3 * y ^ 2) := by
      funext y
      rw [dg y, hψ y, div_one]
    rw [hfun]
    have hc1 : ContinuousAt (fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2))
        1 := by fun_prop
    have h1 : (fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2)) 1 = 0 := by
      norm_num
    have ht : Tendsto (fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2))
        (𝓝[<] (1 : ℝ))
        (𝓝 ((fun y : ℝ => (y * (1 - y)) * (2 * y - 3 * y ^ 2)) 1)) :=
      hc1.tendsto.mono_left nhdsWithin_le_nhds
    rw [h1] at ht
    exact ht
  have hgf0 : Tendsto (fun y : ℝ => (fun x => x ^ 2 * (1 - x)) y *
      (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x ^ 2 * (1 - x)) y *
        (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y ^ 2 * (1 - y)) * (1 - 2 * y) := by
      funext y
      rw [df y, hψ y, div_one]
    rw [hfun]
    have hc0 : ContinuousAt (fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y))
        0 := by fun_prop
    have h0 : (fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y)) 0 = 0 := by
      norm_num
    have ht : Tendsto (fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y)) 0)) :=
      hc0.tendsto.mono_left nhdsWithin_le_nhds
    rw [h0] at ht
    exact ht
  have hgf1 : Tendsto (fun y : ℝ => (fun x => x ^ 2 * (1 - x)) y *
      (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x ^ 2 * (1 - x)) y *
        (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y ^ 2 * (1 - y)) * (1 - 2 * y) := by
      funext y
      rw [df y, hψ y, div_one]
    rw [hfun]
    have hc1 : ContinuousAt (fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y))
        1 := by fun_prop
    have h1 : (fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y)) 1 = 0 := by
      norm_num
    have ht : Tendsto (fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y))
        (𝓝[<] (1 : ℝ))
        (𝓝 ((fun y : ℝ => (y ^ 2 * (1 - y)) * (1 - 2 * y)) 1)) :=
      hc1.tendsto.mono_left nhdsWithin_le_nhds
    rw [h1] at ht
    exact ht
  have hint_fg : Integrable (fun x : ℝ => (fun x => x * (1 - x)) x *
      diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x ^ 2 * (1 - x)) x)
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    have hfun : (fun x : ℝ => (fun x => x * (1 - x)) x * diffusionGenerator
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x => x ^ 2 * (1 - x)) x) =
        fun x => (x * (1 - x)) * (1 - 3 * x) := by
      funext x
      rw [hLg x]
    rw [hfun]
    have h_ae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (speedDensityFrom
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x))
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
      simp only [hσ]
      exact aemeasurable_const
    have h_lt : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ENNReal.ofReal
        (speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) < ∞ := by
      simp only [hσ]
      exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    simp only [speedMeasureFrom]
    rw [integrable_withDensity_iff_integrable_smul₀' h_ae h_lt]
    have hsmul : (fun x : ℝ => (ENNReal.ofReal (speedDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) x)).toReal •
        (fun x' : ℝ => (x' * (1 - x')) * (1 - 3 * x')) x) =
        fun x => 2 * ((x * (1 - x)) * (1 - 3 * x)) := by
      funext x
      rw [hσ x, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [smul_eq_mul]
    rw [hsmul]
    have hcont : Continuous
        (fun x : ℝ => 2 * ((x * (1 - x)) * (1 - 3 * x))) := by fun_prop
    have hIcc : IntegrableOn
        (fun x : ℝ => 2 * ((x * (1 - x)) * (1 - 3 * x))) (Icc (0 : ℝ) 1)
        volume :=
      hcont.integrableOn_Icc
    have hIoo := hIcc.mono_set Ioo_subset_Icc_self
    exact hIoo
  have hint_gf : Integrable (fun x : ℝ => (fun x => x ^ 2 * (1 - x)) x *
      diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x * (1 - x)) x)
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    have hfun : (fun x : ℝ => (fun x => x ^ 2 * (1 - x)) x * diffusionGenerator
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x => x * (1 - x)) x) =
        fun x => (x ^ 2 * (1 - x)) * (-1) := by
      funext x
      rw [hLf x]
    rw [hfun]
    have h_ae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (speedDensityFrom
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x))
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
      simp only [hσ]
      exact aemeasurable_const
    have h_lt : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ENNReal.ofReal
        (speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) < ∞ := by
      simp only [hσ]
      exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    simp only [speedMeasureFrom]
    rw [integrable_withDensity_iff_integrable_smul₀' h_ae h_lt]
    have hsmul : (fun x : ℝ => (ENNReal.ofReal (speedDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) x)).toReal •
        (fun x' : ℝ => (x' ^ 2 * (1 - x')) * (-1)) x) =
        fun x => 2 * ((x ^ 2 * (1 - x)) * (-1)) := by
      funext x
      rw [hσ x, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [smul_eq_mul]
    rw [hsmul]
    have hcont : Continuous
        (fun x : ℝ => 2 * ((x ^ 2 * (1 - x)) * (-1))) := by fun_prop
    have hIcc : IntegrableOn (fun x : ℝ => 2 * ((x ^ 2 * (1 - x)) * (-1)))
        (Icc (0 : ℝ) 1) volume :=
      hcont.integrableOn_Icc
    have hIoo := hIcc.mono_set Ioo_subset_Icc_self
    exact hIoo
  have hdir : IntervalIntegrable (fun x : ℝ => deriv (fun x => x * (1 - x)) x *
      deriv (fun x => x ^ 2 * (1 - x)) x / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) x) volume 0 1 := by
    have hfun : (fun x : ℝ => deriv (fun x => x * (1 - x)) x *
        deriv (fun x => x ^ 2 * (1 - x)) x / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) x) =
        fun x => (1 - 2 * x) * (2 * x - 3 * x ^ 2) := by
      funext x
      rw [df x, dg x, hψ x, div_one]
    rw [hfun]
    have hcont : Continuous
        (fun x : ℝ => (1 - 2 * x) * (2 * x - 3 * x ^ 2)) := by fun_prop
    exact hcont.intervalIntegrable 0 1
  exact integral_mul_diffusionGenerator_speedMeasureFrom_symm (fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ)) (fun x => x * (1 - x)) (fun x => x ^ 2 * (1 - x)) (1 / 2)
    ha ha_cont hba_cont hc hf hg hfg0 hfg1 hgf0 hgf1 hint_fg hint_gf hdir

example :
    ∫ x, (x * (1 - x)) * diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
        (fun x => x * (1 - x)) x
      ∂(speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) =
      -∫ x in (0 : ℝ)..1, (deriv (fun x : ℝ => x * (1 - x)) x) ^ 2 /
        scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x := by
  have hψ : ∀ x, scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 1 := by
    intro x
    simp [scaleDensityFrom]
  have hσ : ∀ x, speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 2 := by
    intro x
    simp only [speedDensityFrom, hψ, mul_one, div_one]
  have hL : ∀ (u : ℝ → ℝ) (x : ℝ), diffusionGenerator (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) u x = deriv (deriv u) x / 2 := by
    intro u x
    simp only [diffusionGenerator]
    ring
  have ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun _ => (1 : ℝ)) x := by
    intro x _
    exact one_pos
  have ha_cont : ContinuousOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const
  have hba_cont : ContinuousOn (fun x : ℝ => (0 : ℝ) / (1 : ℝ))
      (Ioo (0 : ℝ) 1) := by
    simp only [zero_div]
    exact continuousOn_const
  have hc : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x * (1 - x)) (Icc (0 : ℝ) 1) :=
    contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)
  have df : ∀ y, deriv (fun x : ℝ => x * (1 - x)) y = 1 - 2 * y := by
    intro y
    have h : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 * (1 - y) + y * (0 - 1))
        y :=
      (hasDerivAt_id' (x := y)).mul
        ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub (hasDerivAt_id' (x := y)))
    rw [h.deriv]
    ring
  have ddf : ∀ y, deriv (deriv (fun x : ℝ => x * (1 - x))) y = -2 := by
    intro y
    have hfun : deriv (fun x : ℝ => x * (1 - x)) = fun y => 1 - 2 * y :=
      funext df
    rw [hfun]
    simp
  have hLf : ∀ y, diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x * (1 - x)) y = -1 := by
    intro y
    rw [hL, ddf]
    norm_num
  have hf0 : Tendsto (fun y : ℝ => (fun x => x * (1 - x)) y *
      (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x * (1 - x)) y *
        (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y * (1 - y)) * (1 - 2 * y) := by
      funext y
      rw [df y, hψ y, div_one]
    rw [hfun]
    have hc0 : ContinuousAt (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y))
        0 := by fun_prop
    have h0 : (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 0 = 0 := by norm_num
    have ht : Tendsto (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) (𝓝[>] (0 : ℝ))
        (𝓝 ((fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 0)) :=
      hc0.tendsto.mono_left nhdsWithin_le_nhds
    rw [h0] at ht
    exact ht
  have hf1 : Tendsto (fun y : ℝ => (fun x => x * (1 - x)) y *
      (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x * (1 - x)) y *
        (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y * (1 - y)) * (1 - 2 * y) := by
      funext y
      rw [df y, hψ y, div_one]
    rw [hfun]
    have hc1 : ContinuousAt (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y))
        1 := by fun_prop
    have h1 : (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 1 = 0 := by norm_num
    have ht : Tendsto (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) (𝓝[<] (1 : ℝ))
        (𝓝 ((fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 1)) :=
      hc1.tendsto.mono_left nhdsWithin_le_nhds
    rw [h1] at ht
    exact ht
  have hint : Integrable (fun x : ℝ => (fun x => x * (1 - x)) x *
      diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x * (1 - x)) x)
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    have hfun : (fun x : ℝ => (fun x => x * (1 - x)) x * diffusionGenerator
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x => x * (1 - x)) x) =
        fun x => (x * (1 - x)) * (-1) := by
      funext x
      rw [hLf x]
    rw [hfun]
    have h_ae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (speedDensityFrom
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x))
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
      simp only [hσ]
      exact aemeasurable_const
    have h_lt : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ENNReal.ofReal
        (speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) < ∞ := by
      simp only [hσ]
      exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    simp only [speedMeasureFrom]
    rw [integrable_withDensity_iff_integrable_smul₀' h_ae h_lt]
    have hsmul : (fun x : ℝ => (ENNReal.ofReal (speedDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) x)).toReal •
        (fun x' : ℝ => (x' * (1 - x')) * (-1)) x) =
        fun x => 2 * ((x * (1 - x)) * (-1)) := by
      funext x
      rw [hσ x, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [smul_eq_mul]
    rw [hsmul]
    have hcont : Continuous (fun x : ℝ => 2 * ((x * (1 - x)) * (-1))) := by
      fun_prop
    have hIcc : IntegrableOn (fun x : ℝ => 2 * ((x * (1 - x)) * (-1)))
        (Icc (0 : ℝ) 1) volume :=
      hcont.integrableOn_Icc
    have hIoo := hIcc.mono_set Ioo_subset_Icc_self
    exact hIoo
  have hdir : IntervalIntegrable (fun x : ℝ => (deriv (fun x => x * (1 - x)) x)
      ^ 2 / scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x)
      volume 0 1 := by
    have hfun : (fun x : ℝ => (deriv (fun x => x * (1 - x)) x) ^ 2 /
        scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) =
        fun x => (1 - 2 * x) ^ 2 := by
      funext x
      rw [df x, hψ x, div_one]
    rw [hfun]
    have hcont : Continuous (fun x : ℝ => (1 - 2 * x) ^ 2) := by fun_prop
    exact hcont.intervalIntegrable 0 1
  exact integral_mul_diffusionGenerator_speedMeasureFrom_self (fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ)) (fun x => x * (1 - x)) (1 / 2) ha ha_cont hba_cont hc hf
    hf0 hf1 hint hdir

example :
    ∫ x, (x * (1 - x)) * diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
        (fun x => x * (1 - x)) x
      ∂(speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) ≤ 0 := by
  have hψ : ∀ x, scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 1 := by
    intro x
    simp [scaleDensityFrom]
  have hσ : ∀ x, speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x
      = 2 := by
    intro x
    simp only [speedDensityFrom, hψ, mul_one, div_one]
  have hL : ∀ (u : ℝ → ℝ) (x : ℝ), diffusionGenerator (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) u x = deriv (deriv u) x / 2 := by
    intro u x
    simp only [diffusionGenerator]
    ring
  have ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun _ => (1 : ℝ)) x := by
    intro x _
    exact one_pos
  have ha_cont : ContinuousOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const
  have hba_cont : ContinuousOn (fun x : ℝ => (0 : ℝ) / (1 : ℝ))
      (Ioo (0 : ℝ) 1) := by
    simp only [zero_div]
    exact continuousOn_const
  have hc : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x * (1 - x)) (Icc (0 : ℝ) 1) :=
    contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)
  have df : ∀ y, deriv (fun x : ℝ => x * (1 - x)) y = 1 - 2 * y := by
    intro y
    have h : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 * (1 - y) + y * (0 - 1))
        y :=
      (hasDerivAt_id' (x := y)).mul
        ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub (hasDerivAt_id' (x := y)))
    rw [h.deriv]
    ring
  have ddf : ∀ y, deriv (deriv (fun x : ℝ => x * (1 - x))) y = -2 := by
    intro y
    have hfun : deriv (fun x : ℝ => x * (1 - x)) = fun y => 1 - 2 * y :=
      funext df
    rw [hfun]
    simp
  have hLf : ∀ y, diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x * (1 - x)) y = -1 := by
    intro y
    rw [hL, ddf]
    norm_num
  have hf0 : Tendsto (fun y : ℝ => (fun x => x * (1 - x)) y *
      (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x * (1 - x)) y *
        (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y * (1 - y)) * (1 - 2 * y) := by
      funext y
      rw [df y, hψ y, div_one]
    rw [hfun]
    have hc0 : ContinuousAt (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y))
        0 := by fun_prop
    have h0 : (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 0 = 0 := by norm_num
    have ht : Tendsto (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) (𝓝[>] (0 : ℝ))
        (𝓝 ((fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 0)) :=
      hc0.tendsto.mono_left nhdsWithin_le_nhds
    rw [h0] at ht
    exact ht
  have hf1 : Tendsto (fun y : ℝ => (fun x => x * (1 - x)) y *
      (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ)) (1 / 2) y)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun : (fun y : ℝ => (fun x => x * (1 - x)) y *
        (deriv (fun x => x * (1 - x)) y / scaleDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) y)) =
        fun y => (y * (1 - y)) * (1 - 2 * y) := by
      funext y
      rw [df y, hψ y, div_one]
    rw [hfun]
    have hc1 : ContinuousAt (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y))
        1 := by fun_prop
    have h1 : (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 1 = 0 := by norm_num
    have ht : Tendsto (fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) (𝓝[<] (1 : ℝ))
        (𝓝 ((fun y : ℝ => (y * (1 - y)) * (1 - 2 * y)) 1)) :=
      hc1.tendsto.mono_left nhdsWithin_le_nhds
    rw [h1] at ht
    exact ht
  have hint : Integrable (fun x : ℝ => (fun x => x * (1 - x)) x *
      diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x => x * (1 - x)) x)
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    have hfun : (fun x : ℝ => (fun x => x * (1 - x)) x * diffusionGenerator
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x => x * (1 - x)) x) =
        fun x => (x * (1 - x)) * (-1) := by
      funext x
      rw [hLf x]
    rw [hfun]
    have h_ae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (speedDensityFrom
        (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x))
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
      simp only [hσ]
      exact aemeasurable_const
    have h_lt : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ENNReal.ofReal
        (speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) < ∞ := by
      simp only [hσ]
      exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    simp only [speedMeasureFrom]
    rw [integrable_withDensity_iff_integrable_smul₀' h_ae h_lt]
    have hsmul : (fun x : ℝ => (ENNReal.ofReal (speedDensityFrom (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (1 / 2) x)).toReal •
        (fun x' : ℝ => (x' * (1 - x')) * (-1)) x) =
        fun x => 2 * ((x * (1 - x)) * (-1)) := by
      funext x
      rw [hσ x, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [smul_eq_mul]
    rw [hsmul]
    have hcont : Continuous (fun x : ℝ => 2 * ((x * (1 - x)) * (-1))) := by
      fun_prop
    have hIcc : IntegrableOn (fun x : ℝ => 2 * ((x * (1 - x)) * (-1)))
        (Icc (0 : ℝ) 1) volume :=
      hcont.integrableOn_Icc
    have hIoo := hIcc.mono_set Ioo_subset_Icc_self
    exact hIoo
  have hdir : IntervalIntegrable (fun x : ℝ => (deriv (fun x => x * (1 - x)) x)
      ^ 2 / scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x)
      volume 0 1 := by
    have hfun : (fun x : ℝ => (deriv (fun x => x * (1 - x)) x) ^ 2 /
        scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x) =
        fun x => (1 - 2 * x) ^ 2 := by
      funext x
      rw [df x, hψ x, div_one]
    rw [hfun]
    have hcont : Continuous (fun x : ℝ => (1 - 2 * x) ^ 2) := by fun_prop
    exact hcont.intervalIntegrable 0 1
  exact integral_mul_diffusionGenerator_speedMeasureFrom_self_nonpos
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x => x * (1 - x)) (1 / 2) ha
    ha_cont hba_cont hc hf hf0 hf1 hint hdir

#print axioms integral_mul_diffusionGenerator_speedMeasureFrom
#print axioms integral_mul_diffusionGenerator_speedMeasureFrom_symm
#print axioms integral_mul_diffusionGenerator_speedMeasureFrom_self
#print axioms integral_mul_diffusionGenerator_speedMeasureFrom_self_nonpos

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.DirichletForm
