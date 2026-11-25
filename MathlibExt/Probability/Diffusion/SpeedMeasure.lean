/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
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

This module introduces the scale density, speed density, and speed measure of a
one-dimensional diffusion on `(0, 1)` with drift `b` and variance coefficient `a`,
normalized at an interior basepoint `c` following Karlin and Taylor (1981),
Chapter 15, and the flux form of integrals against the speed measure.

## Mathematics

The scale density normalized at `c` is `s(y) = exp(-∫ c..y 2 * b / a)`, the speed
density is `m(x) = 2 / (a x * s x)`, and the speed measure is `m(x) dx` on `(0, 1)`.
When the integrand `2 * b / a` is interval integrable on the interval between two
basepoints, changing the basepoint multiplies the scale density by the corresponding
positive exponential constant and divides the speed density by the same constant. No
such rescaling is asserted for arbitrary coefficients, where the defining integral can
degenerate to its junk value. Unlike a normalization at an endpoint, the
interior-basepoint normalization stays meaningful when `b / a` is not integrable at the
endpoints, as for the Wright-Fisher diffusion with positive mutation rates
`2 * b / a = θ₁ / x - θ₂ / (1 - x)`; see Ewens (2004), Chapter 4.

If a flux `F` has derivative `m * g` on `(0, 1)` and one-sided limits `L0` at `0` and
`L1` at `1`, then `∫ g dm = L1 - L0`. For the generator `L f = (a / 2) f'' + b f'` the
flux `f' / s` has derivative `m * L f` where `a > 0`, so this is the boundary-flux form
of weak stationarity of the speed measure.

All analytic statements use local hypotheses on `(0, 1)` only: positivity and
continuity of `a`, and continuity of `b / a`.

## Main results

* `scaleDensityFrom`, `speedDensityFrom`, `speedMeasureFrom`: the scale density, speed
  density, and speed measure normalized at the basepoint `c`.
* `hasDerivAt_scaleDensityFrom`: `s' = -(2 * b / a) * s` on `(0, 1)`.
* `integral_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto`: the flux form of
  integrals against the speed measure.

## Conventions

The state space is the open interval `(0, 1)`, seen as a set of reals. One-sided
limits at the endpoints use the filters `𝓝[>] 0` and `𝓝[<] 1`.

## What is not claimed

Analytic statements about the densities and the speed measure only. Nothing here
asserts invariance of any constructed process law, finiteness of the speed measure,
reversibility, or any boundary classification.

## References

- Karlin, S. and Taylor, H. M. (1981). *A Second Course in Stochastic
  Processes*. Academic Press, Chapter 15.
- Ewens, W. J. (2004). *Mathematical Population Genetics 1: Theoretical
  Introduction* (2nd edition). Springer, Chapter 4.
-/

open Real Set Filter MeasureTheory
open scoped Topology

@[expose] public section
namespace MathlibExt.Probability.Diffusion

/-- Scale density of a one-dimensional diffusion with drift `b` and variance
coefficient `a`, normalized at basepoint `c`: `exp(-∫ z in c..y, 2 * b z /
a z)`. For `c = 0` this is the normalization at the left endpoint; an interior `c`
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
  have h := (intervalIntegral.integral_hasDerivAt_right hseg hmeas hcont_at).neg.exp
  rw [mul_comm] at h
  exact h

/-- The basepoint speed density is positive at interior points where the
variance coefficient is positive. -/
theorem speedDensityFrom_pos (b a : ℝ → ℝ) (c x : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < speedDensityFrom b a c x := by
  unfold speedDensityFrom
  exact div_pos (by norm_num) (mul_pos (ha_pos x hx) (scaleDensityFrom_pos b a c x))

/-- Flux form of integrals against the basepoint speed measure: if `F` has
derivative `speedDensityFrom b a c x * g x` at every `x ∈ Ioo 0 1`, with one-sided
limits `L0` at `0` and `L1` at `1`, and `g` is integrable against
`speedMeasureFrom b a c`, then `∫ g d(speedMeasureFrom b a c) = L1 - L0`. Each
hypothesis is used: `ha_pos`, `ha_cont`, `hdiv_cont` and `hc` make the speed density
positive and continuous on `(0, 1)`, so that the speed measure has a measurable density
and the integral becomes `∫₀¹ m g`; `hF`, `h0` and `h1` evaluate that integral by the
fundamental theorem of calculus; `hint` makes the integral meaningful. No global
integrability of `b / a` is assumed. With `g` the generator of the diffusion and `F` the
flux `deriv f / scaleDensityFrom b a c`, this is the boundary-flux weak-stationarity
identity. -/
theorem integral_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto (b a g F : ℝ → ℝ)
    (c L0 L1 : ℝ) (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hF : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (speedDensityFrom b a c x * g x) x)
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 L0)) (h1 : Tendsto F (𝓝[<] 1) (𝓝 L1))
    (hint : Integrable g (speedMeasureFrom b a c)) :
    ∫ x, g x ∂(speedMeasureFrom b a c) = L1 - L0 := by
  unfold speedMeasureFrom at hint ⊢
  have hψcont : ContinuousOn (scaleDensityFrom b a c) (Ioo (0:ℝ) 1) := fun x hx =>
    (hasDerivAt_scaleDensityFrom b a c x hdiv_cont hx hc).continuousAt.continuousWithinAt
  have hρcont : ContinuousOn (speedDensityFrom b a c) (Ioo (0:ℝ) 1) :=
    continuousOn_const.div (ha_cont.mul hψcont) fun x hx =>
      mul_ne_zero (ha_pos x hx).ne' (scaleDensityFrom_pos b a c x).ne'
  have hDae : AEMeasurable (fun x => ENNReal.ofReal (speedDensityFrom b a c x))
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable'
      (hρcont.aemeasurable measurableSet_Ioo)
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (0:ℝ) 1)),
      ENNReal.ofReal (speedDensityFrom b a c x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have aeEq : (fun x => (ENNReal.ofReal (speedDensityFrom b a c x)).toReal • g x)
      =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] fun x => speedDensityFrom b a c x * g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [ENNReal.toReal_ofReal (speedDensityFrom_pos b a c x ha_pos hx).le, smul_eq_mul]
  have hDint : Integrable (fun x => speedDensityFrom b a c x * g x)
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    ((integrable_withDensity_iff_integrable_smul₀' hDae hflt).mp hint).congr aeEq
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hF
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hDint) h0 h1
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hFTC
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDae hflt _, integral_congr_ae aeEq]
  exact hFTC

end MathlibExt.Probability.Diffusion
