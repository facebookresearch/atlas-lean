/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SpeedDensity
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.OrderClosed

/-!
# Weak stationarity of regular diffusions against the speed measure

For a one-dimensional regular diffusion with drift `b` and variance `a`, the generator in
canonical form `L f = (1 / m) (f' / ψ)'` (`diffusionGenerator_eq_one_div_speedDensity`)
integrates against the speed measure `m` (`speedMeasure`) to the net boundary flux of
`f' / ψ` between `1` and `0`: `(L f) * m = (f' / ψ)'` on `(0, 1)`, so only the endpoint
flux values survive. These theorems cover the `IsRegularDiffusion` class (scale finite at
both boundaries; includes the neutral and genic-selection Wright-Fisher drifts, and
infinite-speed-mass examples). The Beta-mutation weak stationarity
`integral_mutationGenerator_betaMeasure` is a parallel singular-endpoint result that these
theorems do not subsume.

## Main results

* `integral_diffusionGenerator_speedMeasure`: `∫ L f ∂m = L1 - L0` for the boundary flux
  limits `L0` at `0` and `L1` at `1`.
* `integral_diffusionGenerator_speedMeasure_eq_zero`: `∫ L f ∂m = 0` when both boundary
  fluxes vanish.

## References

* S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*,
  Academic Press, 1981, Chapter 15 (generators in canonical form; speed measure).
-/

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- **Weak stationarity against the speed measure (boundary-flux form).** For a regular
diffusion with drift `b` and variance `a`, the integral of `L f` against the speed measure
`m` is the net boundary flux of `f' / ψ`: `∫ L f ∂m = L1 - L0`, where `L0` (resp. `L1`) is
the one-sided limit of `f' / ψ` at `0` from the right (resp. at `1` from the left). The
identity is the integrated canonical form `L f = (1 / m) (f' / ψ)'`
(`diffusionGenerator_eq_one_div_speedDensity`): against `m`, the integrand is the derivative
`(f' / ψ)'`, so only the endpoint flux values survive. `IsRegularDiffusion` gives positivity
of `a` and `ψ` on `(0, 1)`; `ContDiffOn 2` makes `L f` continuous there with `deriv`
agreeing with the one-sided derivatives; the flux limits supply the boundary values; and
integrability makes the integral a genuine value. This is analytic stationarity only: no
invariance of any process law, no reversibility or Dirichlet-form identity, and no claim
that the speed measure is finite. -/
theorem integral_diffusionGenerator_speedMeasure {b a f : ℝ → ℝ} {L0 L1 : ℝ}
    (h : IsRegularDiffusion b a) (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (h0 : Tendsto (fun y => deriv f y / scaleDensity b a y) (𝓝[>] 0) (𝓝 L0))
    (h1 : Tendsto (fun y => deriv f y / scaleDensity b a y) (𝓝[<] 1) (𝓝 L1))
    (hint : Integrable (diffusionGenerator b a f) (speedMeasure b a)) :
    ∫ x, diffusionGenerator b a f x ∂(speedMeasure b a) = L1 - L0 := by
  unfold speedMeasure at hint ⊢
  have hψcont : ContinuousOn (scaleDensity b a) (Ioo (0:ℝ) 1) :=
    h.continuousOn_scaleDensity.mono Ioo_subset_Icc_self
  have hden : ContinuousOn (fun x => a x * scaleDensity b a x) (Ioo (0:ℝ) 1) :=
    h.continuousOn.mul hψcont
  have hρcont : ContinuousOn (speedDensity b a) (Ioo (0:ℝ) 1) := by
    have hdiv : ContinuousOn (fun x => 2 / (a x * scaleDensity b a x))
        (Ioo (0:ℝ) 1) :=
      continuousOn_const.div hden
        (fun x hx => mul_ne_zero (h.pos x hx).ne' (scaleDensity_pos b a x).ne')
    exact hdiv
  have hDae : AEMeasurable (fun x => ENNReal.ofReal (speedDensity b a x))
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable'
      (hρcont.aemeasurable measurableSet_Ioo)
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (0:ℝ) 1)),
      ENNReal.ofReal (speedDensity b a x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hfIoo : ContDiffOn ℝ 2 f (Ioo (0:ℝ) 1) := hf.mono Ioo_subset_Icc_self
  have hfderiv : ContDiffOn ℝ 1 (deriv f) (Ioo (0:ℝ) 1) :=
    hfIoo.deriv_of_isOpen isOpen_Ioo (by decide)
  have hDf : DifferentiableOn ℝ (deriv f) (Ioo (0:ℝ) 1) :=
    hfderiv.differentiableOn_one
  have hψdiff : DifferentiableOn ℝ (scaleDensity b a) (Ioo (0:ℝ) 1) := by
    intro x hx
    exact (h.hasDerivAt_scaleDensity hx).differentiableAt.differentiableWithinAt
  have hF : DifferentiableOn ℝ (fun y => deriv f y / scaleDensity b a y)
      (Ioo (0:ℝ) 1) :=
    hDf.div hψdiff (fun x hx => (scaleDensity_pos b a x).ne')
  have hderiv : ∀ x ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun y => deriv f y / scaleDensity b a y)
        (deriv (fun y => deriv f y / scaleDensity b a y) x) x := by
    intro x hx
    exact (hF.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have aeEq : (fun x => (ENNReal.ofReal (speedDensity b a x)).toReal •
        diffusionGenerator b a f x)
      =ᵐ[volume.restrict (Ioo (0:ℝ) 1)]
      (fun x => deriv (fun y => deriv f y / scaleDensity b a y) x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hρx : 0 < speedDensity b a x := speedDensity_pos_of_isRegular h hx
    have hρne : speedDensity b a x ≠ 0 := hρx.ne'
    have hL := diffusionGenerator_eq_one_div_speedDensity h hDf hx
    simp only [ENNReal.toReal_ofReal hρx.le, hL, smul_eq_mul]
    field_simp [hρne]
  have hmul : Integrable (fun x => (ENNReal.ofReal (speedDensity b a x)).toReal •
      diffusionGenerator b a f x) (volume.restrict (Ioo (0:ℝ) 1)) :=
    (integrable_withDensity_iff_integrable_smul₀' hDae hflt).mp hint
  have hDint : Integrable (fun x => deriv (fun y => deriv f y / scaleDensity b a y) x)
      (volume.restrict (Ioo (0:ℝ) 1)) := hmul.congr aeEq
  have hinterv : IntervalIntegrable
      (fun x => deriv (fun y => deriv f y / scaleDensity b a y) x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hDint
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDae hflt _]
  have hFTC : (∫ y in (0:ℝ)..1, deriv (fun y => deriv f y / scaleDensity b a y) y)
      = L1 - L0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv
      hinterv h0 h1
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at hFTC
  rw [MeasureTheory.integral_congr_ae aeEq]
  exact hFTC

/-- **Weak stationarity against the speed measure (zero-flux case).** For a regular diffusion, `f`
twice continuously differentiable on `[0, 1]` and `L f` integrable against the speed measure, when
both boundary fluxes vanish, `∫ L f ∂m = 0`: the case `L0 = L1 = 0` of
`integral_diffusionGenerator_speedMeasure`. The Beta-mutation weak stationarity
`integral_mutationGenerator_betaMeasure` is a parallel singular-endpoint result that this
does not subsume. As above, this is analytic stationarity only, with no process-level,
reversibility, or finiteness claim. -/
theorem integral_diffusionGenerator_speedMeasure_eq_zero {b a f : ℝ → ℝ}
    (h : IsRegularDiffusion b a) (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (h0 : Tendsto (fun y => deriv f y / scaleDensity b a y) (𝓝[>] 0) (𝓝 0))
    (h1 : Tendsto (fun y => deriv f y / scaleDensity b a y) (𝓝[<] 1) (𝓝 0))
    (hint : Integrable (diffusionGenerator b a f) (speedMeasure b a)) :
    ∫ x, diffusionGenerator b a f x ∂(speedMeasure b a) = 0 := by
  have hmain := integral_diffusionGenerator_speedMeasure h hf h0 h1 hint
  simpa using hmain

end MathlibExt.Biology.PopulationGenetics.Diffusion
