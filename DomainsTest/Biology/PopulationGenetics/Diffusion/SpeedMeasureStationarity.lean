/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SpeedMeasureStationarity
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology
open MathlibExt.Biology.PopulationGenetics.Diffusion

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SpeedMeasureStationarity

example :
    ∫ x, diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) (fun x => x ^ 2) x
      ∂(speedMeasure (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) = 2 := by
  have hreg : IsRegularDiffusion (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x _
      exact zero_lt_one
    · exact continuousOn_const
    · refine ContinuousOn.congr (continuousOn_const (c := (0:ℝ))) ?_
      intro x _
      simp
    · simpa only [zero_div] using
        intervalIntegrable_const (a := (0:ℝ)) (b := (1:ℝ)) (μ := MeasureTheory.volume)
  have hψ : ∀ x : ℝ, scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x = 1 := by
    intro x
    unfold scaleDensity
    simp
  have hρ2 : ∀ x : ℝ, speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x = 2 := by
    intro x
    unfold speedDensity
    simp only [hψ x]
    norm_num
  have hderiv1 : ∀ x : ℝ, deriv (fun x : ℝ => x ^ 2) x = 2 * x := by
    intro x
    rw [(hasDerivAt_pow 2 x).deriv]
    simp
  have hderiv2 : ∀ x : ℝ, deriv (deriv (fun x : ℝ => x ^ 2)) x = 2 := by
    have hfun : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := funext hderiv1
    intro x
    rw [hfun]
    have h2x : deriv (fun x : ℝ => 2 * x) x = 2 * 1 :=
      ((hasDerivAt_id x).const_mul (2:ℝ)).deriv
    rw [h2x]
    norm_num
  have hgen : ∀ x : ℝ, diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ))
      (fun x : ℝ => x ^ 2) x = 1 := by
    intro x
    unfold diffusionGenerator
    simp only [hderiv1, hderiv2]
    ring
  have hflux : (fun y : ℝ => deriv (fun x : ℝ => x ^ 2) y
      / scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) y)
      = fun y => 2 * y := by
    funext y
    simp only [hderiv1, hψ, div_one]
  have h0 : Tendsto (fun y : ℝ => deriv (fun x : ℝ => x ^ 2) y
      / scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) y) (𝓝[>] 0) (𝓝 0) := by
    rw [hflux]
    have hcont : ContinuousAt (fun y : ℝ => 2 * y) 0 := by fun_prop
    have h : Tendsto (fun y : ℝ => 2 * y) (𝓝[>] 0)
        (𝓝 ((fun y : ℝ => 2 * y) 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have h1 : Tendsto (fun y : ℝ => deriv (fun x : ℝ => x ^ 2) y
      / scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) y) (𝓝[<] 1) (𝓝 2) := by
    rw [hflux]
    have hcont : ContinuousAt (fun y : ℝ => 2 * y) 1 := by fun_prop
    have h : Tendsto (fun y : ℝ => 2 * y) (𝓝[<] 1)
        (𝓝 ((fun y : ℝ => 2 * y) 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x ^ 2) (Icc (0:ℝ) 1) :=
    (contDiff_id.pow 2).contDiffOn
  have hDae : AEMeasurable (fun x : ℝ => ENNReal.ofReal
      (speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x))
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    have hconst : (fun x : ℝ => ENNReal.ofReal
        (speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x))
        = fun _ => ENNReal.ofReal 2 := by
      funext x
      rw [hρ2 x]
    rw [hconst]
    exact aemeasurable_const
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (0:ℝ) 1)),
      ENNReal.ofReal (speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hint : Integrable (diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ))
      (fun x : ℝ => x ^ 2)) (speedMeasure (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) := by
    have hcongr : diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ))
        (fun x : ℝ => x ^ 2) = fun _ => 1 := funext hgen
    rw [hcongr]
    unfold speedMeasure
    rw [integrable_withDensity_iff_integrable_smul₀' hDae hflt]
    have hbase : Integrable (fun _ => (2:ℝ))
        (volume.restrict (Ioo (0:ℝ) 1)) := by
      have hcts : ContinuousOn (fun _ : ℝ => (2:ℝ)) (Icc (0:ℝ) 1) :=
        continuousOn_const
      have hIcc : Integrable (fun _ : ℝ => (2:ℝ))
          (volume.restrict (Icc (0:ℝ) 1)) :=
        hcts.integrableOn_compact isCompact_Icc
      have hIoo := (integrableOn_Icc_iff_integrableOn_Ioo).mp hIcc
      exact hIoo
    refine hbase.congr ?_
    filter_upwards with x
    simp only [hρ2 x, ENNReal.toReal_ofReal zero_le_two, smul_eq_mul, mul_one]
  have hmain := integral_diffusionGenerator_speedMeasure hreg hf h0 h1 hint
  simpa using hmain

example :
    ∫ x, diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ))
        (fun x => x ^ 2 * (1 - x) ^ 2) x
      ∂(speedMeasure (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) = 0 := by
  have hreg : IsRegularDiffusion (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x _
      exact zero_lt_one
    · exact continuousOn_const
    · refine ContinuousOn.congr (continuousOn_const (c := (0:ℝ))) ?_
      intro x _
      simp
    · simpa only [zero_div] using
        intervalIntegrable_const (a := (0:ℝ)) (b := (1:ℝ)) (μ := MeasureTheory.volume)
  have hψ : ∀ x : ℝ, scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x = 1 := by
    intro x
    unfold scaleDensity
    simp
  have hρ2 : ∀ x : ℝ, speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x = 2 := by
    intro x
    unfold speedDensity
    simp only [hψ x]
    norm_num
  have hderiv : ∀ x : ℝ, deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) x
      = 2 * x * (1 - x) * (1 - 2 * x) := by
    intro x
    have hexpand : (fun x : ℝ => x ^ 2 * (1 - x) ^ 2)
        = fun x => x ^ 4 - 2 * x ^ 3 + x ^ 2 := by
      funext y
      ring
    rw [hexpand]
    have h4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * x ^ 3) x := by
      have h := hasDerivAt_pow 4 x
      simpa using h
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
      have h := hasDerivAt_pow 3 x
      simpa using h
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      have h := hasDerivAt_pow 2 x
      simpa using h
    have hc : HasDerivAt (fun x : ℝ => 2 * x ^ 3) (2 * (3 * x ^ 2)) x :=
      h3.const_mul 2
    have hsub : HasDerivAt (fun x : ℝ => x ^ 4 - 2 * x ^ 3)
        (4 * x ^ 3 - 2 * (3 * x ^ 2)) x := h4.sub hc
    have hadd : HasDerivAt (fun x : ℝ => x ^ 4 - 2 * x ^ 3 + x ^ 2)
        (4 * x ^ 3 - 2 * (3 * x ^ 2) + 2 * x) x := hsub.add h2
    have hde : deriv (fun x : ℝ => x ^ 4 - 2 * x ^ 3 + x ^ 2) x
        = 4 * x ^ 3 - 2 * (3 * x ^ 2) + 2 * x := hadd.deriv
    rw [hde]
    ring
  have hderiv2nd : ∀ x : ℝ, deriv (deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2)) x
      = 2 - 12 * x + 12 * x ^ 2 := by
    have hfun : deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2)
        = fun x => 2 * x * (1 - x) * (1 - 2 * x) := funext hderiv
    intro x
    rw [hfun]
    have hexpand : (fun x : ℝ => 2 * x * (1 - x) * (1 - 2 * x))
        = fun x => 2 * x - 6 * x ^ 2 + 4 * x ^ 3 := by
      funext y
      ring
    rw [hexpand]
    have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
    have h2x : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) x := hid.const_mul 2
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      have h := hasDerivAt_pow 2 x
      simpa using h
    have h6 : HasDerivAt (fun x : ℝ => 6 * x ^ 2) (6 * (2 * x)) x :=
      hsq.const_mul 6
    have hcb : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
      have h := hasDerivAt_pow 3 x
      simpa using h
    have h4c : HasDerivAt (fun x : ℝ => 4 * x ^ 3) (4 * (3 * x ^ 2)) x :=
      hcb.const_mul 4
    have hsub : HasDerivAt (fun x : ℝ => 2 * x - 6 * x ^ 2)
        (2 * 1 - 6 * (2 * x)) x := h2x.sub h6
    have hadd : HasDerivAt (fun x : ℝ => 2 * x - 6 * x ^ 2 + 4 * x ^ 3)
        (2 * 1 - 6 * (2 * x) + 4 * (3 * x ^ 2)) x := hsub.add h4c
    have hde : deriv (fun x : ℝ => 2 * x - 6 * x ^ 2 + 4 * x ^ 3) x
        = 2 * 1 - 6 * (2 * x) + 4 * (3 * x ^ 2) := hadd.deriv
    rw [hde]
    ring
  have hgen : ∀ x : ℝ, diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ))
      (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) x = 1 - 6 * x + 6 * x ^ 2 := by
    intro x
    unfold diffusionGenerator
    simp only [hderiv, hderiv2nd]
    ring
  have hflux : (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) y
      / scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) y)
      = fun y => 2 * y * (1 - y) * (1 - 2 * y) := by
    funext y
    simp only [hderiv, hψ, div_one]
  have h0 : Tendsto (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) y
      / scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) y) (𝓝[>] 0) (𝓝 0) := by
    rw [hflux]
    have hcont : ContinuousAt (fun y : ℝ => 2 * y * (1 - y) * (1 - 2 * y)) 0 := by
      fun_prop
    have h : Tendsto (fun y : ℝ => 2 * y * (1 - y) * (1 - 2 * y)) (𝓝[>] 0)
        (𝓝 ((fun y : ℝ => 2 * y * (1 - y) * (1 - 2 * y)) 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have h1 : Tendsto (fun y : ℝ => deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) y
      / scaleDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) y) (𝓝[<] 1) (𝓝 0) := by
    rw [hflux]
    have hcont : ContinuousAt (fun y : ℝ => 2 * y * (1 - y) * (1 - 2 * y)) 1 := by
      fun_prop
    have h : Tendsto (fun y : ℝ => 2 * y * (1 - y) * (1 - 2 * y)) (𝓝[<] 1)
        (𝓝 ((fun y : ℝ => 2 * y * (1 - y) * (1 - 2 * y)) 1)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) (Icc (0:ℝ) 1) :=
    ((contDiff_id.pow 2).mul
      (((contDiff_const (c := (1:ℝ))).sub contDiff_id).pow 2)).contDiffOn
  have hDae : AEMeasurable (fun x : ℝ => ENNReal.ofReal
      (speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x))
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    have hconst : (fun x : ℝ => ENNReal.ofReal
        (speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x))
        = fun _ => ENNReal.ofReal 2 := by
      funext x
      rw [hρ2 x]
    rw [hconst]
    exact aemeasurable_const
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (0:ℝ) 1)),
      ENNReal.ofReal (speedDensity (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hint : Integrable (diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ))
      (fun x : ℝ => x ^ 2 * (1 - x) ^ 2))
      (speedMeasure (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) := by
    have hcongr : diffusionGenerator (fun _ => (0:ℝ)) (fun _ => (1:ℝ))
        (fun x : ℝ => x ^ 2 * (1 - x) ^ 2)
        = fun x => 1 - 6 * x + 6 * x ^ 2 := funext hgen
    rw [hcongr]
    unfold speedMeasure
    rw [integrable_withDensity_iff_integrable_smul₀' hDae hflt]
    have hbase : Integrable (fun x : ℝ => 2 * (1 - 6 * x + 6 * x ^ 2))
        (volume.restrict (Ioo (0:ℝ) 1)) := by
      have hcts : ContinuousOn
          (fun x : ℝ => 2 * (1 - 6 * x + 6 * x ^ 2)) (Icc (0:ℝ) 1) := by
        fun_prop
      have hIcc : Integrable (fun x : ℝ => 2 * (1 - 6 * x + 6 * x ^ 2))
          (volume.restrict (Icc (0:ℝ) 1)) :=
        hcts.integrableOn_compact isCompact_Icc
      have hIoo := (integrableOn_Icc_iff_integrableOn_Ioo).mp hIcc
      exact hIoo
    refine hbase.congr ?_
    filter_upwards with x
    simp only [hρ2 x, ENNReal.toReal_ofReal zero_le_two, smul_eq_mul]
  exact integral_diffusionGenerator_speedMeasure_eq_zero hreg hf h0 h1 hint

#print axioms integral_diffusionGenerator_speedMeasure
#print axioms integral_diffusionGenerator_speedMeasure_eq_zero

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SpeedMeasureStationarity
