/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.SpeedMeasure
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration by parts against the interior-basepoint speed measure

For a one-dimensional diffusion on `(0, 1)` with drift `b` and variance coefficient `a`, let
`m = speedDensityFrom b a c` be the speed density and `speedMeasureFrom b a c` the speed measure,
normalized at an interior basepoint `c`. If `Q` has derivative `m * h` on `(0, 1)`, then
integrating `f * Q' = m * (f * h)` by parts gives
`∫ f * h d(speedMeasureFrom b a c) = [f * Q]₀¹ - ∫₀¹ f' * Q`, with the boundary term given by
one-sided limits from inside `(0, 1)`.

For the generator `L g = (a / 2) g'' + b g'`, the flux `Q = g' / s` of `g`, with `s` the scale
density, has derivative `m * L g` on `(0, 1)`, so this is the Dirichlet-form identity
`∫ f * L g dm = [f * g' / s]₀¹ - ∫₀¹ f' * g' / s`.

## Main results

* `integral_mul_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto`: integration by parts
  against the speed measure, with explicit endpoint limits `B0` and `B1`.

## What is not claimed

An analytic identity on functions with the stated regularity only. It does not claim an `L²`
generator closure, self-adjointness as an operator statement, a semigroup, or reversibility of
any constructed process.

## References

* S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*,
  Academic Press, 1981, Chapter 15.
-/

open Set Filter MeasureTheory
open scoped Topology

@[expose] public section
namespace MathlibExt.Probability.Diffusion

/-- Integration by parts against the interior-basepoint speed measure: if `Q` has derivative
`speedDensityFrom b a c x * h x` at every `x ∈ Ioo 0 1`, `f` is differentiable on `(0, 1)`, and
`f * Q` has one-sided limits `B0` at `0` and `B1` at `1`, then
`∫ f * h d(speedMeasureFrom b a c) = (B1 - B0) - ∫₀¹ f' * Q`.

Each hypothesis is used: `ha_pos`, `ha_cont`, `hdiv_cont` and `hc` make the speed density
positive and continuous on `(0, 1)`, so that the integral against the speed measure becomes
`∫₀¹ m * f * h`; `hf` and `hQ` give the derivative `f' * Q + f * m * h` of `f * Q`; `hB0` and
`hB1` are the boundary limits; `hint` makes the left-hand integral meaningful and `hdir` the
integral on the right. No global integrability of `b / a` is assumed. With `h` the generator
applied to `g` and `Q` the flux `deriv g / scaleDensityFrom b a c`, this is the Dirichlet-form
identity of the diffusion. -/
theorem integral_mul_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto (b a f h Q : ℝ → ℝ)
    (c B0 B1 : ℝ) (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : DifferentiableOn ℝ f (Ioo 0 1))
    (hQ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Q (speedDensityFrom b a c x * h x) x)
    (hB0 : Tendsto (fun y => f y * Q y) (𝓝[>] 0) (𝓝 B0))
    (hB1 : Tendsto (fun y => f y * Q y) (𝓝[<] 1) (𝓝 B1))
    (hint : Integrable (fun x => f x * h x) (speedMeasureFrom b a c))
    (hdir : IntervalIntegrable (fun x => deriv f x * Q x) volume 0 1) :
    ∫ x, f x * h x ∂(speedMeasureFrom b a c) =
      (B1 - B0) - ∫ x in (0 : ℝ)..1, deriv f x * Q x := by
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
  have aeEq : (fun x => (ENNReal.ofReal (speedDensityFrom b a c x)).toReal • (f x * h x))
      =ᵐ[volume.restrict (Ioo (0:ℝ) 1)]
      fun x => f x * (speedDensityFrom b a c x * h x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [ENNReal.toReal_ofReal (speedDensityFrom_pos b a c x ha_pos hx).le, smul_eq_mul]
    ring
  have hD : IntervalIntegrable (fun x => f x * (speedDensityFrom b a c x * h x)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (((integrable_withDensity_iff_integrable_smul₀' hDae hflt).mp hint).congr aeEq)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y => f y * Q y)
      (deriv f x * Q x + f x * (speedDensityFrom b a c x * h x)) x := fun x hx =>
    (hf.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt.mul (hQ x hx)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv
    (hdir.add hD) hB0 hB1
  rw [intervalIntegral.integral_add hdir hD] at hFTC
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDae hflt _, integral_congr_ae aeEq,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, ← hFTC]
  ring

end MathlibExt.Probability.Diffusion
