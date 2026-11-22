/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SpeedDensity
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order

/-!
# Interior-basepoint scale density, speed density, and speed measure

This module introduces the scale density, speed density, and speed measure
of a one-dimensional diffusion on `(0, 1)`, normalized at an interior
basepoint `c` following Karlin and Taylor (1981), Chapter 15. It is intended
to live at
`Domains/Biology/PopulationGenetics/Diffusion/SingularSpeedMeasure.lean`.

## Mathematics

For drift `b` and variance coefficient `a`, the scale density normalized at
`c` is `s(y) = exp(-∫ c..y 2 * b / a)`, the speed density is
`m(x) = 2 / (a x * s x)`, and the speed measure is `m(x) dx` on `(0, 1)`.
When the integrand `2 * b / a` is interval integrable on the interval
between two basepoints, changing the basepoint multiplies the scale
density by the corresponding positive exponential constant and divides
the speed density by the same constant. No such rescaling is asserted
for arbitrary coefficients, where the defining integral can degenerate
to its junk value. Unlike the zero-origin normalization, the interior-basepoint
normalization stays meaningful when `b / a` is not integrable at the
endpoints, which is the positive-mutation Wright-Fisher case
`2 * b / a = θ₁ / x - θ₂ / (1 - x)`; see Ewens (2004), Chapter 4.

All analytic statements use local hypotheses on `(0, 1)` only: positivity
and continuity of `a`, and continuity of `b / a`.

## Conventions

The state space is the open interval `(0, 1)`, seen as a set of reals. The
flux of a test function `f` is `deriv f / scaleDensityFrom`. One-sided
limits at the endpoints use the filters `𝓝[>] 0` and `𝓝[<] 1`.

## What is not claimed

Analytic weak stationarity against the speed measure only. Nothing here
asserts invariance of any constructed process law, finiteness of the speed
measure, reversibility, or any boundary classification.

## References

- Karlin, S. and Taylor, H. M. (1981). *A Second Course in Stochastic
  Processes*. Academic Press, Chapter 15.
- Ewens, W. J. (2004). *Mathematical Population Genetics 1: Theoretical
  Introduction* (2nd edition). Springer, Chapter 4.
-/

open Real Set Filter MeasureTheory
open scoped Topology

@[expose] public section
namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Scale density of a one-dimensional diffusion with drift `b` and variance
coefficient `a`, normalized at basepoint `c`: `exp(-∫ z in c..y, 2 * b z /
a z)`. For `c = 0` this is the zero-origin `scaleDensity`; general `c`
keeps the integral meaningful when `b / a` blows up at the endpoints. No
regularity of `b`, `a`, or position of `c` is assumed. -/
noncomputable def scaleDensityFrom (b a : ℝ → ℝ) (c y : ℝ) : ℝ :=
  exp (-∫ z in c..y, 2 * b z / a z)

/-- Speed density `2 / (a x * scaleDensityFrom b a c x)`. Positive where
`a` is positive; see `speedDensityFrom_pos`. Its basepoint dependence is
the reciprocal of the scale density's, and rescaling under a change of
basepoint requires interval integrability of `2 * b / a` between the
basepoints. -/
noncomputable def speedDensityFrom (b a : ℝ → ℝ) (c x : ℝ) : ℝ :=
  2 / (a x * scaleDensityFrom b a c x)

/-- Speed measure on `(0, 1)`: Lebesgue measure restricted to `Ioo 0 1`
with density `speedDensityFrom b a c`. Finiteness is not claimed. -/
noncomputable def speedMeasureFrom (b a : ℝ → ℝ) (c : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity
    (fun x => ENNReal.ofReal (speedDensityFrom b a c x))

/-- The basepoint scale density is everywhere positive: it is an
exponential. No hypotheses are needed. -/
theorem scaleDensityFrom_pos (b a : ℝ → ℝ) (c y : ℝ) :
    0 < scaleDensityFrom b a c y := by
  unfold scaleDensityFrom
  exact Real.exp_pos _

/-- Derivative of the basepoint scale density at an interior point: with
`b / a` continuous on `(0, 1)`, `scaleDensityFrom b a c` has derivative
`-(2 * b x / a x) * scaleDensityFrom b a c x` at `x ∈ Ioo 0 1`. The
hypothesis `hc` keeps the basepoint interior: for an endpoint basepoint
with a non-integrable `b / a`, the defining integral degenerates to its
junk value and the scale density collapses to `1`. -/
theorem hasDerivAt_scaleDensityFrom (b a : ℝ → ℝ) (c x : ℝ)
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (scaleDensityFrom b a c)
      (-(2 * b x / a x) * scaleDensityFrom b a c x) x := by
  have hg_cont : ContinuousOn (fun z => 2 * b z / a z) (Ioo (0:ℝ) 1) := by
    have h2 : ContinuousOn (fun z => 2 * (b z / a z)) (Ioo (0:ℝ) 1) :=
      continuousOn_const.mul hdiv_cont
    have hfun : (fun z => 2 * b z / a z) = fun z => 2 * (b z / a z) := by
      funext z
      exact mul_div_assoc _ _ _
    rwa [hfun]
  have hseg : IntervalIntegrable (fun z => 2 * b z / a z) volume c x := by
    rcases le_total c x with hcx | hxc
    · have hsub : Icc c x ⊆ Ioo (0:ℝ) 1 := by
        intro y hy
        exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
      exact (hg_cont.mono hsub).intervalIntegrable_of_Icc hcx
    · have hsub : Icc x c ⊆ Ioo (0:ℝ) 1 := by
        intro y hy
        exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hc.2⟩
      exact ((hg_cont.mono hsub).intervalIntegrable_of_Icc hxc).symm
  have hcont_at : ContinuousAt (fun z => 2 * b z / a z) x :=
    hg_cont.continuousAt (isOpen_Ioo.mem_nhds hx)
  have hmeas : StronglyMeasurableAtFilter (fun z => 2 * b z / a z) (𝓝 x) :=
    ⟨Ioo (0:ℝ) 1, isOpen_Ioo.mem_nhds hx,
      hg_cont.aestronglyMeasurable measurableSet_Ioo⟩
  have hFTC := intervalIntegral.integral_hasDerivAt_right hseg hmeas hcont_at
  have h : HasDerivAt (fun y => Real.exp (-∫ z in c..y, 2 * b z / a z))
      (Real.exp (-∫ z in c..x, 2 * b z / a z) * -(2 * b x / a x)) x :=
    hFTC.neg.exp
  have hder : Real.exp (-∫ z in c..x, 2 * b z / a z) * -(2 * b x / a x)
      = -(2 * b x / a x) * Real.exp (-∫ z in c..x, 2 * b z / a z) := by
    ring
  rw [hder] at h
  show HasDerivAt (fun y => Real.exp (-∫ z in c..y, 2 * b z / a z))
    (-(2 * b x / a x) * Real.exp (-∫ z in c..x, 2 * b z / a z)) x
  exact h

/-- The basepoint speed density is positive at interior points where the
variance coefficient is positive. -/
theorem speedDensityFrom_pos (b a : ℝ → ℝ) (c x : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < speedDensityFrom b a c x := by
  unfold speedDensityFrom
  exact div_pos (by norm_num) (mul_pos (ha_pos x hx) (scaleDensityFrom_pos b a c x))

/-- Canonical divergence form of the generator: where `a > 0`, `b / a` is
continuous, and `deriv f` is differentiable, `diffusionGenerator b a f x =
(1 / speedDensityFrom b a c x) * deriv (deriv f / scaleDensityFrom) x`.
The hypothesis `hc` keeps the basepoint interior: for an endpoint
basepoint with a non-integrable `b / a`, the defining integral degenerates
to its junk value and the scale density collapses to `1`. This is the
pointwise identity behind the flux form of the weak-stationarity integral. -/
theorem diffusionGenerator_eq_one_div_speedDensityFrom (b a f : ℝ → ℝ)
    (c x : ℝ) (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hf : DifferentiableOn ℝ (deriv f) (Ioo 0 1)) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    diffusionGenerator b a f x = (1 / speedDensityFrom b a c x) *
      deriv (fun y => deriv f y / scaleDensityFrom b a c y) x := by
  have hax : a x ≠ 0 := (ha_pos x hx).ne'
  have hψx : scaleDensityFrom b a c x ≠ 0 :=
    (scaleDensityFrom_pos b a c x).ne'
  have hmul : a x * scaleDensityFrom b a c x ≠ 0 := mul_ne_zero hax hψx
  have hψ : HasDerivAt (scaleDensityFrom b a c)
      (-(2 * b x / a x) * scaleDensityFrom b a c x) x :=
    hasDerivAt_scaleDensityFrom b a c x hdiv_cont hx hc
  have hdf : DifferentiableAt ℝ (deriv f) x :=
    hf.differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hF : HasDerivAt (fun y => deriv f y / scaleDensityFrom b a c y)
      ((deriv (deriv f) x * scaleDensityFrom b a c x -
        deriv f x * (-(2 * b x / a x) * scaleDensityFrom b a c x)) /
        (scaleDensityFrom b a c x) ^ 2) x :=
    hdf.hasDerivAt.div hψ hψx
  have hderiv := hF.deriv
  rw [hderiv]
  unfold diffusionGenerator
  unfold speedDensityFrom
  field_simp
  ring

/-- Boundary-flux weak-stationarity identity: the integral of
`diffusionGenerator b a f` against `speedMeasureFrom b a c` equals the net
flux `L1 - L0`. Each hypothesis is used: `ha_pos` and `hdiv_cont` give the
canonical form of the generator; `ha_cont` keeps the speed density
continuous; `hc` keeps the basepoint interior so the connecting segments
avoid the singular endpoints, giving a continuously-differentiable scale
density and a continuous speed density on `(0, 1)`; `hf` gives
twice-differentiable test functions up to the boundary;
`h0` and `h1` are the boundary flux limits; `hint` makes the integral
meaningful. No global integrability of `b / a` is assumed. Only analytic
stationarity is claimed: no process law, reversibility, or boundary
classification. -/
theorem integral_diffusionGenerator_speedMeasureFrom (b a f : ℝ → ℝ)
    (c L0 L1 : ℝ) (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (h0 : Tendsto (fun y => deriv f y / scaleDensityFrom b a c y) (𝓝[>] 0)
      (𝓝 L0))
    (h1 : Tendsto (fun y => deriv f y / scaleDensityFrom b a c y) (𝓝[<] 1)
      (𝓝 L1))
    (hint : Integrable (diffusionGenerator b a f) (speedMeasureFrom b a c)) :
    ∫ x, diffusionGenerator b a f x ∂(speedMeasureFrom b a c) = L1 - L0 := by
  unfold speedMeasureFrom at hint ⊢
  have hψdiff : DifferentiableOn ℝ (scaleDensityFrom b a c) (Ioo (0:ℝ) 1) := by
    intro x hx
    exact (hasDerivAt_scaleDensityFrom b a c x hdiv_cont hx
      hc).differentiableAt.differentiableWithinAt
  have hψcont : ContinuousOn (scaleDensityFrom b a c) (Ioo (0:ℝ) 1) :=
    hψdiff.continuousOn
  have hden : ContinuousOn (fun x => a x * scaleDensityFrom b a c x)
      (Ioo (0:ℝ) 1) :=
    ha_cont.mul hψcont
  have hρcont : ContinuousOn (speedDensityFrom b a c) (Ioo (0:ℝ) 1) := by
    have hdiv : ContinuousOn (fun x => 2 / (a x * scaleDensityFrom b a c x))
        (Ioo (0:ℝ) 1) :=
      continuousOn_const.div hden
        (fun x hx => mul_ne_zero (ha_pos x hx).ne'
          (scaleDensityFrom_pos b a c x).ne')
    exact hdiv
  have hDae : AEMeasurable (fun x => ENNReal.ofReal (speedDensityFrom b a c x))
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable'
      (hρcont.aemeasurable measurableSet_Ioo)
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (0:ℝ) 1)),
      ENNReal.ofReal (speedDensityFrom b a c x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hfIoo : ContDiffOn ℝ 2 f (Ioo (0:ℝ) 1) := hf.mono Ioo_subset_Icc_self
  have hfderiv : ContDiffOn ℝ 1 (deriv f) (Ioo (0:ℝ) 1) :=
    hfIoo.deriv_of_isOpen isOpen_Ioo (by decide)
  have hDf : DifferentiableOn ℝ (deriv f) (Ioo (0:ℝ) 1) :=
    hfderiv.differentiableOn_one
  have hF : DifferentiableOn ℝ (fun y => deriv f y / scaleDensityFrom b a c y)
      (Ioo (0:ℝ) 1) :=
    hDf.div hψdiff (fun x hx => (scaleDensityFrom_pos b a c x).ne')
  have hderiv : ∀ x ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun y => deriv f y / scaleDensityFrom b a c y)
        (deriv (fun y => deriv f y / scaleDensityFrom b a c y) x) x := by
    intro x hx
    exact (hF.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have aeEq : (fun x => (ENNReal.ofReal (speedDensityFrom b a c x)).toReal •
        diffusionGenerator b a f x)
      =ᵐ[volume.restrict (Ioo (0:ℝ) 1)]
      (fun x => deriv (fun y => deriv f y / scaleDensityFrom b a c y) x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hρx : 0 < speedDensityFrom b a c x :=
      speedDensityFrom_pos b a c x ha_pos hx
    have hρne : speedDensityFrom b a c x ≠ 0 := hρx.ne'
    have hL := diffusionGenerator_eq_one_div_speedDensityFrom b a f c x ha_pos
      hdiv_cont hDf hx hc
    simp only [ENNReal.toReal_ofReal hρx.le, hL, smul_eq_mul]
    field_simp [hρne]
  have hmul : Integrable (fun x => (ENNReal.ofReal (speedDensityFrom b a c x)).toReal •
      diffusionGenerator b a f x) (volume.restrict (Ioo (0:ℝ) 1)) :=
    (integrable_withDensity_iff_integrable_smul₀' hDae hflt).mp hint
  have hDint : Integrable (fun x => deriv (fun y => deriv f y / scaleDensityFrom b a c y) x)
      (volume.restrict (Ioo (0:ℝ) 1)) := hmul.congr aeEq
  have hinterv : IntervalIntegrable
      (fun x => deriv (fun y => deriv f y / scaleDensityFrom b a c y) x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hDint
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDae hflt _]
  have hFTC : (∫ y in (0:ℝ)..1, deriv (fun y => deriv f y / scaleDensityFrom b a c y) y)
      = L1 - L0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv
      hinterv h0 h1
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at hFTC
  rw [MeasureTheory.integral_congr_ae aeEq]
  exact hFTC

/-- Zero-flux corollary: when both boundary fluxes vanish, the generator
integrates to zero against the speed measure. Hypotheses are as in
`integral_diffusionGenerator_speedMeasureFrom`. -/
theorem integral_diffusionGenerator_speedMeasureFrom_eq_zero (b a f : ℝ → ℝ)
    (c : ℝ) (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (h0 : Tendsto (fun y => deriv f y / scaleDensityFrom b a c y) (𝓝[>] 0)
      (𝓝 (0 : ℝ)))
    (h1 : Tendsto (fun y => deriv f y / scaleDensityFrom b a c y) (𝓝[<] 1)
      (𝓝 (0 : ℝ)))
    (hint : Integrable (diffusionGenerator b a f) (speedMeasureFrom b a c)) :
    ∫ x, diffusionGenerator b a f x ∂(speedMeasureFrom b a c) = 0 := by
  have hmain := integral_diffusionGenerator_speedMeasureFrom b a f c 0 0 ha_pos
    ha_cont hdiv_cont hc hf h0 h1 hint
  simpa using hmain

end MathlibExt.Biology.PopulationGenetics.Diffusion
