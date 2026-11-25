/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Domains.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
public import MathlibExt.Probability.Diffusion.DirichletForm
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Order.OrderClosed

/-!
# Dirichlet form of a one-dimensional diffusion

This file states the integration-by-parts identity for a one-dimensional
diffusion generator against its interior-basepoint speed measure, together
with the symmetry (reversibility on the stated core) and the nonpositivity of
the quadratic form that follow when the boundary flux vanishes.

## Setup

Let `L = diffusionGenerator b a` be the generator with drift `b` and diffusion
coefficient `a`, `ψ = scaleDensityFrom b a c` the scale density with interior
basepoint `c ∈ (0, 1)`, and `speedMeasureFrom b a c` the speed measure. The
scale density and the speed measure are generic and live in
`MathlibExt.Probability.Diffusion.SpeedMeasure`; the companion module
`Domains.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure` re-exports
them into this namespace and gives the canonical form
`f * L g * (speed density) = f * (g' / ψ)'` on `(0, 1)`. Integration by parts
against the speed measure,
`integral_mul_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto` in
`MathlibExt.Probability.Diffusion.DirichletForm`, then gives
`∫ f * L g ∂(speed measure) = [f * (g' / ψ)]₀¹ - ∫₀¹ (f' * g') / ψ`. All test
functions are `ContDiffOn ℝ 2` on the closed interval `Icc 0 1`; endpoint flux
limits are one-sided, taken from inside `(0, 1)`.

## Main results

* `integral_mul_diffusionGenerator_speedMeasureFrom`: the integration-by-parts
  identity with explicit endpoint flux limits `B0`, `B1`.
* `integral_mul_diffusionGenerator_speedMeasureFrom_symm`: symmetry
  `∫ f * L g = ∫ g * L f` when both fluxes vanish.
* `integral_mul_diffusionGenerator_speedMeasureFrom_self`: the quadratic case
  `∫ f * L f = -∫₀¹ (f')² / ψ` with vanishing flux.
* `integral_mul_diffusionGenerator_speedMeasureFrom_self_nonpos`: the
  nonpositivity `∫ f * L f ≤ 0`.

## Non-goals

These are integration-by-parts identities on the stated smooth core against
the speed measure. They do not claim an `L²` generator closure,
self-adjointness as an operator statement, a semigroup, detailed balance for a
constructed process, or stochastic reversibility of paths.

## References

* S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*,
  Academic Press, 1981, Chapter 15.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Integration by parts for a one-dimensional diffusion generator against its
interior-basepoint speed measure.

Let `L = diffusionGenerator b a` with drift `b` and diffusion coefficient `a`,
`ψ = scaleDensityFrom b a c` the scale density with interior basepoint `c`,
and `speedMeasureFrom b a c` the speed measure, from the companion module.
The canonical form `f * L g * (speed density) = f * (g' / ψ)'` on `(0, 1)`
gives, by integration by parts, the stated identity: the speed-weighted
integral of `f * L g` equals the boundary flux difference `B1 - B0` minus the
Dirichlet form `∫₀¹ (f' * g') / ψ`.

Hypotheses: `ha` keeps the diffusion nondegenerate on `(0, 1)`, so the
canonical form and the speed density are defined there; `ha_cont` and
`hba_cont` give continuity of the coefficients of `L` on `(0, 1)`; `hc`
places the basepoint strictly inside, so `ψ` is the interior scale density;
`hf` and `hg` provide twice continuous differentiability up to the closed
endpoints, so `L g` and the flux `f * (g' / ψ)` are defined on `[0, 1]`; `hB0`
and `hB1` are the one-sided endpoint limits of the flux from inside the
interval (existence is assumed, since the flux need not extend continuously);
`hint` makes the left-hand integral well defined; `hdir` makes the
Dirichlet-form integral on the right well defined.

This is an identity on the stated smooth core only. It does not claim an `L²`
generator closure, self-adjointness as an operator statement, a semigroup,
detailed balance for a constructed process, or stochastic reversibility. -/
public theorem integral_mul_diffusionGenerator_speedMeasureFrom
    (b a f g : ℝ → ℝ) (c B0 B1 : ℝ)
    (ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hba_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hg : ContDiffOn ℝ 2 g (Icc 0 1))
    (hB0 : Tendsto (fun y => f y * (deriv g y / scaleDensityFrom b a c y))
      (𝓝[>] (0 : ℝ)) (𝓝 B0))
    (hB1 : Tendsto (fun y => f y * (deriv g y / scaleDensityFrom b a c y))
      (𝓝[<] (1 : ℝ)) (𝓝 B1))
    (hint : Integrable (fun x => f x * diffusionGenerator b a g x)
      (speedMeasureFrom b a c))
    (hdir : IntervalIntegrable
      (fun x => deriv f x * deriv g x / scaleDensityFrom b a c x) volume 0 1) :
    ∫ x, f x * diffusionGenerator b a g x ∂(speedMeasureFrom b a c) =
      (B1 - B0) - ∫ x in (0 : ℝ)..1, deriv f x * deriv g x /
        scaleDensityFrom b a c x := by
  have hU : UniqueDiffOn ℝ (Ioo (0 : ℝ) 1) := isOpen_Ioo.uniqueDiffOn
  have hfC1 : ContDiffOn ℝ 1 f (Ioo 0 1) :=
    ((contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin (n := 1)
      hU).mp (hf.mono Ioo_subset_Icc_self)).1
  have hgC1 : ContDiffOn ℝ 1 (iteratedDerivWithin 1 g (Ioo 0 1))
      (Ioo 0 1) :=
    ((contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin (n := 1)
      hU).mp (hg.mono Ioo_subset_Icc_self)).2
  have hgDerivDiff : DifferentiableOn ℝ (deriv g) (Ioo 0 1) := by
    have h := hgC1.differentiableOn_one
    rw [iteratedDerivWithin_one] at h
    exact h.congr (fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm)
  simp only [mul_div_assoc] at hdir ⊢
  refine
    MathlibExt.Probability.Diffusion.integral_mul_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto
      b a f (diffusionGenerator b a g) (fun y => deriv g y / scaleDensityFrom b a c y) c B0 B1
      ha ha_cont hba_cont hc hfC1.differentiableOn_one (fun x hx => ?_) hB0 hB1 hint hdir
  have hQx : DifferentiableAt ℝ (fun y => deriv g y / scaleDensityFrom b a c y) x :=
    (hgDerivDiff.differentiableAt (isOpen_Ioo.mem_nhds hx)).div
      (hasDerivAt_scaleDensityFrom b a c x hba_cont hx hc).differentiableAt
      (scaleDensityFrom_pos b a c x).ne'
  rw [diffusionGenerator_eq_one_div_speedDensityFrom b a g c x ha hba_cont hgDerivDiff hx hc,
    ← mul_assoc, mul_one_div_cancel (speedDensityFrom_pos b a c x ha hx).ne', one_mul]
  exact hQx.hasDerivAt

/-- Symmetry (reversibility on the stated core) of a one-dimensional diffusion
generator against its interior-basepoint speed measure.

Under the setup of `integral_mul_diffusionGenerator_speedMeasureFrom`, when
the boundary flux vanishes at both endpoints for both ordered pairs (`hfg0`
and `hfg1` for `(f, g)`, `hgf0` and `hgf1` for `(g, f)`), the boundary terms
in the integration-by-parts identity are zero on both sides, and the two
Dirichlet forms agree since `f' * g' = g' * f'`. Hence `∫ f * L g = ∫ g * L f`
against `speedMeasureFrom b a c`.

Hypotheses: `ha`, `ha_cont`, `hba_cont`, `hc`, `hf`, `hg` are as in
`integral_mul_diffusionGenerator_speedMeasureFrom`; the four vanishing
endpoint limits remove the boundary terms; `hint_fg` and `hint_gf` make both
weighted integrals well defined; `hdir` makes the shared Dirichlet-form
integral well defined (one ordered pair suffices by commutativity of
multiplication).

This states symmetry of the bilinear form on the stated smooth core, the
analytic content of reversibility here, not operator-level self-adjointness,
semigroup symmetry, detailed balance, or pathwise reversibility. -/
public theorem integral_mul_diffusionGenerator_speedMeasureFrom_symm
    (b a f g : ℝ → ℝ) (c : ℝ)
    (ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hba_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hg : ContDiffOn ℝ 2 g (Icc 0 1))
    (hfg0 : Tendsto (fun y => f y * (deriv g y / scaleDensityFrom b a c y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hfg1 : Tendsto (fun y => f y * (deriv g y / scaleDensityFrom b a c y))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)))
    (hgf0 : Tendsto (fun y => g y * (deriv f y / scaleDensityFrom b a c y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hgf1 : Tendsto (fun y => g y * (deriv f y / scaleDensityFrom b a c y))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)))
    (hint_fg : Integrable (fun x => f x * diffusionGenerator b a g x)
      (speedMeasureFrom b a c))
    (hint_gf : Integrable (fun x => g x * diffusionGenerator b a f x)
      (speedMeasureFrom b a c))
    (hdir : IntervalIntegrable
      (fun x => deriv f x * deriv g x / scaleDensityFrom b a c x) volume 0 1) :
    ∫ x, f x * diffusionGenerator b a g x ∂(speedMeasureFrom b a c) =
      ∫ x, g x * diffusionGenerator b a f x ∂(speedMeasureFrom b a c) := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have e1 := integral_mul_diffusionGenerator_speedMeasureFrom b a f g c 0 0
    ha ha_cont hba_cont hc hf hg hfg0 hfg1 hint_fg hdir
  have hdir2 : IntervalIntegrable
      (fun x => deriv g x * deriv f x / scaleDensityFrom b a c x)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01]
    have h1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp hdir
    have h1' : Integrable
        (fun x => deriv f x * deriv g x / scaleDensityFrom b a c x)
        (volume.restrict (Ioc 0 1)) := h1
    have haeG : (fun x =>
          deriv f x * deriv g x / scaleDensityFrom b a c x) =ᵐ[
          volume.restrict (Ioc 0 1)]
        (fun x => deriv g x * deriv f x / scaleDensityFrom b a c x) :=
      ae_restrict_of_forall_mem measurableSet_Ioc (fun x _ => by
        change deriv f x * deriv g x / scaleDensityFrom b a c x =
          deriv g x * deriv f x / scaleDensityFrom b a c x
        ring)
    exact h1'.congr haeG
  have e2 := integral_mul_diffusionGenerator_speedMeasureFrom b a g f c 0 0
    ha ha_cont hba_cont hc hg hf hgf0 hgf1 hint_gf hdir2
  have hdeq : (∫ x in (0 : ℝ)..1,
        deriv f x * deriv g x / scaleDensityFrom b a c x) =
      (∫ x in (0 : ℝ)..1,
        deriv g x * deriv f x / scaleDensityFrom b a c x) := by
    rw [intervalIntegral.integral_of_le h01,
      intervalIntegral.integral_of_le h01]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => by
      show deriv f x * deriv g x / scaleDensityFrom b a c x =
        deriv g x * deriv f x / scaleDensityFrom b a c x
      ring)
  rw [e1, e2, hdeq]

/-- Dirichlet-form identity for the quadratic form of a one-dimensional
diffusion generator against its interior-basepoint speed measure.

This is `integral_mul_diffusionGenerator_speedMeasureFrom` specialized to
`g = f` with vanishing boundary flux (`hf0`, `hf1`): the speed-weighted
integral of `f * L f` equals minus the Dirichlet energy `∫₀¹ (f')² / ψ`.

Hypotheses: `ha`, `ha_cont`, `hba_cont`, `hc`, `hf` are as in
`integral_mul_diffusionGenerator_speedMeasureFrom`; `hf0` and `hf1` are the
vanishing one-sided endpoint limits of `f * (f' / ψ)` from inside the
interval; `hint` makes the left-hand integral well defined; `hdir` makes the
Dirichlet energy integral on the right well defined.

This is an identity on the stated smooth core only, with no operator-closure,
self-adjointness, semigroup, detailed-balance, or pathwise-reversibility
claim. -/
public theorem integral_mul_diffusionGenerator_speedMeasureFrom_self
    (b a f : ℝ → ℝ) (c : ℝ)
    (ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hba_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hf0 : Tendsto (fun y => f y * (deriv f y / scaleDensityFrom b a c y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hf1 : Tendsto (fun y => f y * (deriv f y / scaleDensityFrom b a c y))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)))
    (hint : Integrable (fun x => f x * diffusionGenerator b a f x)
      (speedMeasureFrom b a c))
    (hdir : IntervalIntegrable
      (fun x => (deriv f x) ^ 2 / scaleDensityFrom b a c x) volume 0 1) :
    ∫ x, f x * diffusionGenerator b a f x ∂(speedMeasureFrom b a c) =
      -∫ x in (0 : ℝ)..1, (deriv f x) ^ 2 / scaleDensityFrom b a c x := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hdir2 : IntervalIntegrable
      (fun x => deriv f x * deriv f x / scaleDensityFrom b a c x)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01]
    have h1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp hdir
    have h1' : Integrable
        (fun x => (deriv f x) ^ 2 / scaleDensityFrom b a c x)
        (volume.restrict (Ioc 0 1)) := h1
    have hae2 : (fun x => (deriv f x) ^ 2 / scaleDensityFrom b a c x)
        =ᵐ[volume.restrict (Ioc 0 1)]
        (fun x => deriv f x * deriv f x / scaleDensityFrom b a c x) :=
      ae_restrict_of_forall_mem measurableSet_Ioc (fun x _ => by
        change (deriv f x) ^ 2 / scaleDensityFrom b a c x =
          deriv f x * deriv f x / scaleDensityFrom b a c x
        ring)
    exact h1'.congr hae2
  have e1 := integral_mul_diffusionGenerator_speedMeasureFrom b a f f c 0 0
    ha ha_cont hba_cont hc hf hf hf0 hf1 hint hdir2
  have hdeq : (∫ x in (0 : ℝ)..1,
        deriv f x * deriv f x / scaleDensityFrom b a c x) =
      (∫ x in (0 : ℝ)..1, (deriv f x) ^ 2 / scaleDensityFrom b a c x) := by
    rw [intervalIntegral.integral_of_le h01,
      intervalIntegral.integral_of_le h01]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => by
      show deriv f x * deriv f x / scaleDensityFrom b a c x =
        (deriv f x) ^ 2 / scaleDensityFrom b a c x
      ring)
  rw [e1, hdeq, sub_self, zero_sub]

/-- Nonpositivity of the quadratic form of a one-dimensional diffusion
generator against its interior-basepoint speed measure.

The Dirichlet energy integrand `(f')² / ψ` is nonnegative everywhere: the
numerator is a square and the scale density `ψ` is strictly positive at every
point (see `scaleDensityFrom_pos` in the companion module, which needs no
hypotheses), so the interval integral is nonnegative and its negation is
nonpositive. The hypotheses are exactly those of
`integral_mul_diffusionGenerator_speedMeasureFrom_self`, stated separately so
the sign conclusion can be used without unfolding the identity.

As with the identity, this is a statement on the smooth core only, not an
operator-level dissipativity or self-adjointness claim. -/
public theorem integral_mul_diffusionGenerator_speedMeasureFrom_self_nonpos
    (b a f : ℝ → ℝ) (c : ℝ)
    (ha : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hba_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 2 f (Icc 0 1))
    (hf0 : Tendsto (fun y => f y * (deriv f y / scaleDensityFrom b a c y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hf1 : Tendsto (fun y => f y * (deriv f y / scaleDensityFrom b a c y))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)))
    (hint : Integrable (fun x => f x * diffusionGenerator b a f x)
      (speedMeasureFrom b a c))
    (hdir : IntervalIntegrable
      (fun x => (deriv f x) ^ 2 / scaleDensityFrom b a c x) volume 0 1) :
    ∫ x, f x * diffusionGenerator b a f x ∂(speedMeasureFrom b a c) ≤ 0 := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have e1 := integral_mul_diffusionGenerator_speedMeasureFrom_self b a f c
    ha ha_cont hba_cont hc hf hf0 hf1 hint hdir
  rw [e1]
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..1,
      (deriv f x) ^ 2 / scaleDensityFrom b a c x :=
    intervalIntegral.integral_nonneg h01 (fun u _ =>
      div_nonneg (sq_nonneg _) (le_of_lt (scaleDensityFrom_pos b a c u)))
  exact neg_nonpos.mpr hnn

end MathlibExt.Biology.PopulationGenetics.Diffusion
