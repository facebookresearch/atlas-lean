/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SpeedDensity
public import MathlibExt.Probability.Diffusion.SpeedMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Order

/-!
# The diffusion generator against the interior-basepoint speed measure

The scale density `scaleDensityFrom`, speed density `speedDensityFrom`, and speed
measure `speedMeasureFrom` of a one-dimensional diffusion on `(0, 1)`, normalized at an
interior basepoint `c`, and the flux form of integrals against the speed measure are
generic and live in `MathlibExt.Probability.Diffusion.SpeedMeasure`; the names are
re-exported into this namespace. This module connects them to the generator
`diffusionGenerator b a f = (a / 2) f'' + b f'` of `GeneralDiffusion`: the canonical
form `L f = (1 / m) (f' / s)'` on `(0, 1)`, from `diffusionGenerator_eq_of_hasDerivAt`,
and the boundary-flux weak-stationarity identity `∫ L f dm = L1 - L0`.

The interior-basepoint normalization keeps these statements meaningful when `b / a` is
not integrable at the endpoints, which is the positive-mutation Wright-Fisher case
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

-- The basepoint scale density, speed density, and speed measure, with their basic lemmas:
-- generic declarations re-exported so that they also resolve in this namespace.
export MathlibExt.Probability.Diffusion (scaleDensityFrom speedDensityFrom speedMeasureFrom
  scaleDensityFrom_pos hasDerivAt_scaleDensityFrom speedDensityFrom_pos)

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
  have hψx : scaleDensityFrom b a c x ≠ 0 := (scaleDensityFrom_pos b a c x).ne'
  rw [diffusionGenerator_eq_of_hasDerivAt hax hψx
    (hasDerivAt_scaleDensityFrom b a c x hdiv_cont hx hc)
    (hf.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt, speedDensityFrom]
  congr 1
  field_simp

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
  have hDf : DifferentiableOn ℝ (deriv f) (Ioo (0:ℝ) 1) :=
    ((hf.mono Ioo_subset_Icc_self).deriv_of_isOpen isOpen_Ioo
      (by decide)).differentiableOn_one
  refine
    MathlibExt.Probability.Diffusion.integral_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto
      b a (diffusionGenerator b a f) (fun y => deriv f y / scaleDensityFrom b a c y) c L0 L1
      ha_pos ha_cont hdiv_cont hc (fun x hx => ?_) h0 h1 hint
  have hFx : DifferentiableAt ℝ (fun y => deriv f y / scaleDensityFrom b a c y) x :=
    (hDf.differentiableAt (isOpen_Ioo.mem_nhds hx)).div
      (hasDerivAt_scaleDensityFrom b a c x hdiv_cont hx hc).differentiableAt
      (scaleDensityFrom_pos b a c x).ne'
  rw [diffusionGenerator_eq_one_div_speedDensityFrom b a f c x ha_pos hdiv_cont hDf hx hc,
    ← mul_assoc, mul_one_div_cancel (speedDensityFrom_pos b a c x ha_pos hx).ne', one_mul]
  exact hFx.hasDerivAt

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
