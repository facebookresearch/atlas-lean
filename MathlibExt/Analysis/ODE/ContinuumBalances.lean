/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import MathlibExt.Analysis.ODE.DirichletSineEigenfunctions
public import MathlibExt.Probability.Diffusion.FokkerPlanckGradient

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Probability.Diffusion.FokkerPlanckFreeEnergy

/-!
# Continuum balances and the one-dimensional diffusion equation

Finite-volume and continuum conservation laws, divergence-form diffusion, explicit steady
and separated solutions, and the energy method for the Dirichlet heat equation.

## i. Overview

All quantities are real coordinates (a concentration or a temperature after a consistent
choice of units); no dimensional-quantity API is used. The balance law and the constitutive
law `q = -D ∂ₓu` are separate hypotheses, and every PDE statement holds only in the function
class written in its hypotheses. Fluxes are positive in the direction of increasing index or
coordinate. In `discreteBalance`, the net gain of a cell is inflow through its left end minus
outflow through its right end. `integralBalance` uses the signed orientation from `a` to `b`;
it describes the amount on the geometric interval `[a, b]` only when `a ≤ b`.

* Finite volumes (A). On a chain of `n` cells of positive width `Δx` with face fluxes
  `F : Fin (n + 1) → ℝ`, the cell rate is `-(F (i + 1) - F i) / Δx`. The width is bundled with
  a proof of strict positivity. The internal fluxes cancel in the sum, and with no-flux
  boundary faces one explicit step `c i + τ * discreteBalance Δx F i` conserves `∑ i, c i`.
* Continuum balance (B). For a jointly `C¹` density `u` and flux `q`, the local law
  `∂ₜu + ∂ₓq = s` between the endpoints gives the oriented identity
  `d/dt ∫ₐᵇ u = q(a) - q(b) + ∫ₐᵇ s`. Reversing the endpoints reverses both signs; it does
  not preserve the unsigned geometric amount. With a variable
  diffusivity `D` and `q = -D ∂ₓu` it reads `∂ₜu = ∂ₓ(D ∂ₓu) + s`, where
  `∂ₓ(D ∂ₓu) = D' ∂ₓu + D ∂ₓₓu` and not `D ∂ₓₓu`: `D x = x`, `u x = x²` give `4x` and `2x`.
  In several dimensions the balance is proved only conditionally: the divergence theorem
  for the domain is the explicit hypothesis `integral_div_eq_boundary`.
* Explicit solutions (C). A function with `u'' = 0` on `[a, b]` is the linear interpolant of
  its Dirichlet data. The separated mode `exp(-D (kπ)² t) √2 sin(kπx)` solves
  `∂ₜu = D ∂ₓₓu` on `[0, 1]` with zero Dirichlet values and initial profile `√2 sin(kπx)`.
* Energy method (D). For a jointly `C²` solution of `∂ₜu = D ∂ₓₓu` with `D ≥ 0` (in particular
  `D > 0`) on `[0, L]` with zero Dirichlet values, `E(t) = ∫₀ᴸ u²` satisfies
  `E'(t) = -2D ∫₀ᴸ (∂ₓu)² ≤ 0`. Hence `E` is nonincreasing for `t ≥ 0`, and two such
  solutions with the same initial data agree on `[0, L]` for all `t ≥ 0`.

Checking that a given function, such as `heatMode`, satisfies the equation, the boundary
values and its own initial data verifies that one solution. It proves neither existence for
arbitrary initial data nor uniqueness outside the class of section D. Not covered: general
PDE existence, the divergence theorem on general domains, completeness of the sine modes,
convergence of numerical schemes (`MathlibExt.Analysis.ODE.ExplicitEuler` is separate), and
other boundary conditions, variable coefficients or nonlinear equations in section D.

The spatial modes are `GreensOperator.sineBasisFun` with the eigenfunction lemmas of
`MathlibExt.Analysis.ODE.DirichletSineEigenfunctions`, and the several-dimensional balance
uses `MathlibExt.Probability.FokkerPlanck.divergence`. Mathlib supplies the fundamental
theorem of calculus, differentiation under the integral sign and a divergence theorem for
rectangular boxes, but no conservation-law, diffusion-equation or energy-method statements.

## ii. Key results

* `totalDiscreteChange_eq`, `sum_add_mul_discreteBalance_of_noFlux`: telescoping and no-flux
  conservation for the finite-volume chain.
* `hasDerivAt_integral_of_localConservation`: the integral balance law.
* `localConservation_diffusiveFlux_iff`, `deriv_mul_deriv`, `deriv_id_mul_deriv_sq`:
  divergence-form diffusion, its product rule, and the counterexample to dropping `D'`.
* `hasDerivAt_setIntegral_of_divergence`: the several-dimensional balance, conditional on
  the divergence theorem.
* `eq_linear_of_hasDerivAt_zero`, `linear_solves_steady`: steady linear profiles.
* `heatMode_heatEquation`, `heatMode_space_zero`, `heatMode_space_one`,
  `heatMode_time_zero`: the separated heat modes.
* `hasDerivAt_heatEnergy`, `deriv_heatEnergy_nonpos`, `antitoneOn_heatEnergy`,
  `heatEquation_unique`: the energy identity, its sign, energy decay and uniqueness.

## iii. Table of contents

- A. Discrete finite-volume balance
- B. Local and integral conservation laws
  - B.1. The one-dimensional integral balance
  - B.2. Divergence-form diffusion with variable diffusivity
  - B.3. Several dimensions, conditional on the divergence theorem
- C. Explicit solutions
  - C.1. Steady linear profiles
  - C.2. Separated heat modes
- D. Energy decay and uniqueness for the Dirichlet heat equation

## iv. References

- ATLAS roadmap module MF08 (track foundations), with planning anchors R10 (the
  `MathlibExt.Analysis.ODE` modules `ExplicitEuler`, `DirichletSineEigenfunctions` and
  `FiniteElement1D`) and R11 (the Mathlib and `MathlibExt` substrate). No textbook source is
  formalized here.
-/

@[expose] public section

open Set MeasureTheory
open MathlibExt.Analysis.ODE.GreensOperator (sineBasisFun)
open MathlibExt.Analysis.ODE.DirichletSineEigenfunctions
open MathlibExt.Probability.FokkerPlanck (divergence)

namespace MathlibExt.Analysis.ODE.ContinuumBalances

/-!

## A. Discrete finite-volume balance

-/

/-- **Finite-volume balance** (MF08.1). Cell `i : Fin n` of a chain of cells of common width
`Δx` lies between the faces `i.castSucc` (left) and `i.succ` (right), and `F j` is the flux
through face `j`, positive towards increasing index; `F 0` and `F (Fin.last n)` are the left
and right boundary fluxes. The concentration in cell `i` changes at the rate
`-(F (i + 1) - F i) / Δx`, inflow minus outflow per unit width. The width is a positive real,
so zero and negative cell widths cannot be supplied to this API. -/
noncomputable def discreteBalance {n : ℕ} (Δx : {x : ℝ // 0 < x})
    (F : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  -(F i.succ - F i.castSucc) / Δx

/-- **Total discrete change** (MF08.1): the sum over all cells of `discreteBalance Δx F`, the
rate of change of the total `∑ i, c i` of the cell concentrations. -/
noncomputable def totalDiscreteChange {n : ℕ} (Δx : {x : ℝ // 0 < x})
    (F : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, discreteBalance Δx F i

private lemma sum_succ_sub_castSucc {n : ℕ} (F : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (F i.succ - F i.castSucc) = F (Fin.last n) - F 0 := by
  cases n with
  | zero => simp
  | succ m => rw [← Finset.Iic_top, Fin.top_eq_last, Fin.sum_Iic_sub, Fin.succ_last]

/-- **Telescoping** (MF08.1): the internal fluxes cancel exactly, so the total discrete change
is the boundary inflow `F 0` minus the boundary outflow `F (Fin.last n)`, per unit width. -/
lemma totalDiscreteChange_eq {n : ℕ} (Δx : {x : ℝ // 0 < x}) (F : Fin (n + 1) → ℝ) :
    totalDiscreteChange Δx F = -(F (Fin.last n) - F 0) / Δx := by
  simp only [totalDiscreteChange, discreteBalance]
  rw [← Finset.sum_div, Finset.sum_neg_distrib, sum_succ_sub_castSucc]

/-- One explicit discrete-balance step `c i ↦ c i + τ * discreteBalance Δx F i` with time step
`τ` changes the total `∑ i, c i` by `τ * totalDiscreteChange Δx F`. -/
lemma sum_add_mul_discreteBalance {n : ℕ} (Δx : {x : ℝ // 0 < x}) (τ : ℝ)
    (c : Fin n → ℝ) (F : Fin (n + 1) → ℝ) :
    ∑ i, (c i + τ * discreteBalance Δx F i) = ∑ i, c i + τ * totalDiscreteChange Δx F := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, totalDiscreteChange]

/-- **No-flux conservation** (MF08.1): if both boundary fluxes vanish, one explicit step
`c i ↦ c i + τ * discreteBalance Δx F i` leaves the total `∑ i, c i` unchanged. -/
lemma sum_add_mul_discreteBalance_of_noFlux {n : ℕ} (Δx : {x : ℝ // 0 < x}) (τ : ℝ)
    (c : Fin n → ℝ)
    {F : Fin (n + 1) → ℝ} (hleft : F 0 = 0) (hright : F (Fin.last n) = 0) :
    ∑ i, (c i + τ * discreteBalance Δx F i) = ∑ i, c i := by
  rw [sum_add_mul_discreteBalance, totalDiscreteChange_eq, hleft, hright]
  simp

/-!

## B. Local and integral conservation laws

### B.1. The one-dimensional integral balance

-/

/-- **Local conservation law** (MF08.2) `∂ₜu + ∂ₓq = s` at the point `(t, x)`, for a density
`u`, a flux `q` (positive towards increasing `x`) and a source `s`, each a function of time
and then space. The partial derivatives are Mathlib `deriv`s, so the predicate carries meaning
together with the differentiability hypotheses, which the lemmas state separately. -/
def localConservation (u q s : ℝ → ℝ → ℝ) (t x : ℝ) : Prop :=
  deriv (fun τ => u τ x) t + deriv (q t) x = s t x

/-- **Oriented integral balance** (MF08.2) from `a` to `b` at time `t`:
`q t a - q t b + ∫ₐᵇ s`. When `a ≤ b`, this is left-boundary inflow minus right-boundary
outflow plus the source on `[a, b]`. When `a > b`, it is the negative of the balance from
`b` to `a`, not the balance of the unsigned geometric interval. -/
noncomputable def integralBalance (q s : ℝ → ℝ → ℝ) (a b t : ℝ) : ℝ :=
  q t a - q t b + ∫ x in a..b, s t x

private lemma hasDerivAt_fst_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E → ℝ} (hu : ContDiff ℝ 1 (Function.uncurry u)) (t : ℝ) (x : E) :
    HasDerivAt (fun τ => u τ x) (fderiv ℝ (Function.uncurry u) (t, x) (1, 0)) t := by
  have h := (hu.differentiable (by norm_num) (t, x)).hasFDerivAt
  simpa [Function.comp_def] using
    h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

private lemma hasDerivAt_snd_of_contDiff {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (t x : ℝ) :
    HasDerivAt (u t) (fderiv ℝ (Function.uncurry u) (t, x) (0, 1)) x := by
  have h := (hu.differentiable (by norm_num) (t, x)).hasFDerivAt
  simpa [Function.comp_def] using
    h.comp_hasDerivAt x ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))

private lemma continuous_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E → ℝ} (hu : ContDiff ℝ 1 (Function.uncurry u)) (v : ℝ × E) :
    Continuous (fun p : ℝ × E => fderiv ℝ (Function.uncurry u) p v) :=
  (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- **Oriented integral balance law** (MF08.2). Let the density `u` and the flux `q` be jointly
`C¹` on `ℝ × ℝ` (time, then space). If `∂ₜu + ∂ₓq = s` holds at time `t` throughout
`uIcc a b = [min a b, max a b]`, the signed integral `∫ₐᵇ u` has time derivative
`q t a - q t b + ∫ₐᵇ s` at `t`. For `a ≤ b`, the integral is the amount on `[a, b]`;
for `a > b`, it is the negative of the amount on `[b, a]`. -/
lemma hasDerivAt_integral_of_localConservation {u q s : ℝ → ℝ → ℝ} {a b t : ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hq : ContDiff ℝ 1 (Function.uncurry q))
    (hlaw : ∀ x ∈ uIcc a b, localConservation u q s t x) :
    HasDerivAt (fun τ => ∫ x in a..b, u τ x) (integralBalance q s a b t) t := by
  set ut : ℝ → ℝ → ℝ := fun τ x => fderiv ℝ (Function.uncurry u) (τ, x) (1, 0)
  set qx : ℝ → ℝ := fun x => fderiv ℝ (Function.uncurry q) (t, x) (0, 1)
  have hut (τ x : ℝ) : HasDerivAt (fun τ' => u τ' x) (ut τ x) τ :=
    hasDerivAt_fst_of_contDiff hu τ x
  have hqx (x : ℝ) : HasDerivAt (q t) (qx x) x := hasDerivAt_snd_of_contDiff hq t x
  have hut_cont : Continuous (Function.uncurry ut) := continuous_fderiv_apply hu (1, 0)
  have hqx_cont : Continuous qx :=
    (continuous_fderiv_apply hq (0, 1)).comp (continuous_const.prodMk continuous_id)
  have hut_t : Continuous (ut t) := hut_cont.comp (continuous_const.prodMk continuous_id)
  have hd := MathlibExt.Probability.FokkerPlanck.integral_hasDerivAt u ut a b t hu.continuous
    hut_cont hut
  have hs : ∫ x in a..b, s t x = ∫ x in a..b, (ut t x + qx x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have h := hlaw x hx
    rw [localConservation, (hut t x).deriv, (hqx x).deriv] at h
    exact h.symm
  have hftc : ∫ x in a..b, qx x = q t b - q t a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hqx x)
      (hqx_cont.intervalIntegrable a b)
  have hval : ∫ x in a..b, ut t x = integralBalance q s a b t := by
    rw [integralBalance, hs, intervalIntegral.integral_add (hut_t.intervalIntegrable a b)
      (hqx_cont.intervalIntegrable a b), hftc]
    ring
  rwa [hval] at hd

/-!

### B.2. Divergence-form diffusion with variable diffusivity

-/

/-- **Diffusive flux** (MF08.2): with the constitutive law `q = -D ∂ₓu` for a diffusivity
`D : ℝ → ℝ`, the local law `∂ₜu + ∂ₓq = s` is the divergence-form equation
`∂ₜu = ∂ₓ(D ∂ₓu) + s`. -/
lemma localConservation_diffusiveFlux_iff {u s : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {t x : ℝ} :
    localConservation u (fun τ y => -(D y * deriv (u τ) y)) s t x ↔
      deriv (fun τ => u τ x) t = deriv (fun y => D y * deriv (u t) y) x + s t x := by
  simp only [localConservation, deriv.fun_neg]
  constructor <;> intro h <;> linarith

/-- **Product rule for the diffusion term** (MF08.2): if `D` and `∂ₓv` are differentiable at
`x`, then `∂ₓ(D ∂ₓv) = D' ∂ₓv + D ∂ₓₓv` at `x`. -/
lemma deriv_mul_deriv {D v : ℝ → ℝ} {x : ℝ} (hD : DifferentiableAt ℝ D x)
    (hv : DifferentiableAt ℝ (deriv v) x) :
    deriv (fun y => D y * deriv v y) x = deriv D x * deriv v x + D x * iteratedDeriv 2 v x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact deriv_fun_mul hD hv

/-- **The term `D' ∂ₓu` cannot be dropped** (MF08.2): for `D x = x` and `u x = x²`,
`∂ₓ(D ∂ₓu) = 4x` while `D ∂ₓₓu = 2x`. -/
lemma deriv_id_mul_deriv_sq (x : ℝ) :
    deriv (fun y : ℝ => y * deriv (fun z : ℝ => z ^ 2) y) x = 4 * x ∧
      x * iteratedDeriv 2 (fun z : ℝ => z ^ 2) x = 2 * x := by
  have h1 : deriv (fun z : ℝ => z ^ 2) = fun z => 2 * z := by
    funext z
    simp
  have h2 : HasDerivAt (fun y : ℝ => y * (2 * y)) (1 * (2 * x) + x * (2 * 1)) x :=
    (hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_mul 2)
  refine ⟨?_, ?_⟩
  · rw [h1, h2.deriv]
    ring
  · rw [iteratedDeriv_succ, iteratedDeriv_one, h1, ((hasDerivAt_id' x).const_mul 2).deriv]
    ring

/-!

### B.3. Several dimensions, conditional on the divergence theorem

-/

/-- **Integral balance in divergence form** (MF08.2), conditional on the divergence theorem.
Let `Ω` be a compact subset of `ℝⁿ = Fin n → ℝ` with Lebesgue measure, let the density `u` be
jointly `C¹`, let `q t` be the flux field at time `t` with divergence
`FokkerPlanck.divergence (q t) = ∑ᵢ ∂ᵢ (q t)ᵢ`, and let `s t` be integrable on `Ω`. If the
local law `∂ₜu + div q = s` holds at time `t` on `Ω`, and `integral_div_eq_boundary` states the
divergence theorem `∫_Ω div q = Φ t` with `Φ t` the outward flux through the boundary, then
`d/dt ∫_Ω u = -Φ t + ∫_Ω s`. The divergence theorem is a hypothesis, not a result.
For `Ω = [a, b]` with `a ≤ b`, the outward flux is `q t b - q t a`, matching
`integralBalance` with increasing endpoint orientation. -/
lemma hasDerivAt_setIntegral_of_divergence {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {u s : ℝ → (Fin n → ℝ) → ℝ} {q : ℝ → (Fin n → ℝ) → Fin n → ℝ} {Φ : ℝ → ℝ} {t : ℝ}
    (hΩ : IsCompact Ω) (hu : ContDiff ℝ 1 (Function.uncurry u)) (hs : IntegrableOn (s t) Ω)
    (hlaw : ∀ x ∈ Ω, deriv (fun τ => u τ x) t + divergence (q t) x = s t x)
    (integral_div_eq_boundary : ∫ x in Ω, divergence (q t) x = Φ t) :
    HasDerivAt (fun τ => ∫ x in Ω, u τ x) (-Φ t + ∫ x in Ω, s t x) t := by
  set ut : ℝ → (Fin n → ℝ) → ℝ := fun τ x => fderiv ℝ (Function.uncurry u) (τ, x) (1, 0)
  have hut (τ : ℝ) (x : Fin n → ℝ) : HasDerivAt (fun τ' => u τ' x) (ut τ x) τ :=
    hasDerivAt_fst_of_contDiff hu τ x
  have hut_cont : Continuous (Function.uncurry ut) := continuous_fderiv_apply hu (1, 0)
  have hut_t : Continuous (ut t) := hut_cont.comp (continuous_const.prodMk continuous_id)
  have hfin : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hΩ :
    IsCompact (Icc (t - 1) (t + 1) ×ˢ Ω)).exists_bound_of_continuousOn hut_cont.continuousOn
  have hc (τ : ℝ) : Continuous (u τ) :=
    hu.continuous.comp (continuous_const.prodMk continuous_id)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict Ω)
    (bound := fun _ => C) (Icc_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Filter.Eventually.of_forall fun τ => (hc τ).aestronglyMeasurable)
    ((hc t).continuousOn.integrableOn_compact hΩ) hut_t.aestronglyMeasurable
    ((ae_restrict_iff' hΩ.measurableSet).2
      (Filter.Eventually.of_forall fun x hx τ hτ => hC (τ, x) ⟨hτ, hx⟩))
    (integrable_const C) (ae_of_all _ fun x τ _ => hut τ x)).2
  have hut_int : IntegrableOn (ut t) Ω := hut_t.continuousOn.integrableOn_compact hΩ
  have hdiv_eq : EqOn (fun x => s t x - ut t x) (divergence (q t)) Ω := fun x hx => by
    have h := hlaw x hx
    rw [(hut t x).deriv] at h
    simp only
    linarith
  have hdiv : IntegrableOn (divergence (q t)) Ω :=
    (hs.sub hut_int).congr_fun hdiv_eq hΩ.measurableSet
  have hval : ∫ x in Ω, ut t x = -Φ t + ∫ x in Ω, s t x := by
    rw [setIntegral_congr_fun hΩ.measurableSet (g := fun x => s t x - divergence (q t) x)
      fun x hx => by
        have h := hdiv_eq hx
        simp only at h ⊢
        linarith, integral_sub hs hdiv, integral_div_eq_boundary]
    ring
  rwa [hval] at hd

/-!

## C. Explicit solutions

### C.1. Steady linear profiles

-/

/-- **Steady profiles are linear** (MF08.3): if `u` has derivative `u'` on `[a, b]` and `u'`
has derivative `0` there (so `u'' = 0`), with Dirichlet values `u a = uA` and `u b = uB`,
then `u` is the linear interpolant `uA + (uB - uA) (x - a) / (b - a)` on `[a, b]`. -/
lemma eq_linear_of_hasDerivAt_zero {u u' : ℝ → ℝ} {a b uA uB : ℝ} (hab : a < b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x) (hu' : ∀ x ∈ Icc a b, HasDerivAt u' 0 x)
    (ha : u a = uA) (hb : u b = uB) {x : ℝ} (hx : x ∈ Icc a b) :
    u x = uA + (uB - uA) * (x - a) / (b - a) := by
  have hconst : ∀ y ∈ Icc a b, u' y = u' a :=
    constant_of_has_deriv_right_zero (fun y hy => (hu' y hy).continuousAt.continuousWithinAt)
      fun y hy => (hu' y (Ico_subset_Icc_self hy)).hasDerivWithinAt
  have hlin : ∀ y ∈ Icc a b, u y = u a + u' a * (y - a) := by
    refine eq_of_has_deriv_right_eq (f' := fun _ => u' a) (fun y hy => ?_) (fun y _ => ?_)
      (fun y hy => (hu y hy).continuousAt.continuousWithinAt) ?_ (by simp)
    · rw [← hconst y (Ico_subset_Icc_self hy)]
      exact (hu y (Ico_subset_Icc_self hy)).hasDerivWithinAt
    · simpa using (((hasDerivAt_id' y).sub_const a).const_mul (u' a)).const_add (u a)
        |>.hasDerivWithinAt
    · exact (continuous_const.add
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  have hb' := hlin b ⟨hab.le, le_rfl⟩
  rw [hb, ha] at hb'
  have hm : u' a = (uB - uA) / (b - a) := by
    rw [eq_div_iff (sub_ne_zero.2 hab.ne')]
    linarith
  rw [hlin x hx, ha, hm]
  ring

/-- **The linear profile solves the steady problem** (MF08.3): its second derivative vanishes
everywhere and it takes the Dirichlet values `uA` at `a` and `uB` at `b`. -/
lemma linear_solves_steady {a b uA uB : ℝ} (hab : a ≠ b) :
    (∀ x, iteratedDeriv 2 (fun y => uA + (uB - uA) * (y - a) / (b - a)) x = 0) ∧
      (fun y => uA + (uB - uA) * (y - a) / (b - a)) a = uA ∧
      (fun y => uA + (uB - uA) * (y - a) / (b - a)) b = uB := by
  have hderiv (y : ℝ) : HasDerivAt (fun y => uA + (uB - uA) * (y - a) / (b - a))
      ((uB - uA) / (b - a)) y := by
    simpa [mul_div_right_comm] using
      ((((hasDerivAt_id' y).sub_const a).const_mul (uB - uA)).div_const (b - a)).const_add uA
  have hfun : deriv (fun y => uA + (uB - uA) * (y - a) / (b - a)) =
      fun _ => (uB - uA) / (b - a) := funext fun y => (hderiv y).deriv
  refine ⟨fun x => ?_, by simp, ?_⟩
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hfun, deriv_const]
  · field_simp [sub_ne_zero.2 hab.symm]
    ring

/-!

### C.2. Separated heat modes

-/

/-- **Separated heat mode** (MF08.3): `exp(-D λₖ t) uₖ(x)` on `[0, 1]` (length `L = 1`), with
the Dirichlet eigenfunction `uₖ = sineBasisFun k = √2 sin(kπ ·)` and its eigenvalue
`λₖ = dirichletLaplacianEigenvalue k = (kπ)²`, both reused from `GreensOperator` and
`DirichletSineEigenfunctions`; only the time factor is new. -/
noncomputable def heatMode (D : ℝ) (k : ℕ+) (t x : ℝ) : ℝ :=
  Real.exp (-D * dirichletLaplacianEigenvalue k * t) * sineBasisFun k x

/-- Time derivative of a heat mode: `∂ₜ heatMode = -D λₖ heatMode`. -/
lemma hasDerivAt_heatMode_time (D : ℝ) (k : ℕ+) (t x : ℝ) :
    HasDerivAt (fun τ => heatMode D k τ x)
      (-D * dirichletLaplacianEigenvalue k * heatMode D k t x) t := by
  have h : HasDerivAt (fun τ => heatMode D k τ x)
      (Real.exp (-D * dirichletLaplacianEigenvalue k * t) *
        (-D * dirichletLaplacianEigenvalue k * 1) * sineBasisFun k x) t :=
    (((hasDerivAt_id' t).const_mul _).exp).mul_const _
  convert h using 1
  rw [heatMode]
  ring

/-- Space derivative of a heat mode, from `dirichletSine_hasDerivAt`. -/
lemma hasDerivAt_heatMode_space (D : ℝ) (k : ℕ+) (t x : ℝ) :
    HasDerivAt (heatMode D k t)
      (Real.exp (-D * dirichletLaplacianEigenvalue k * t) * deriv (sineBasisFun k) x) x := by
  rw [dirichletSine_deriv]
  exact (dirichletSine_hasDerivAt k x).const_mul _

/-- Second space derivative of a heat mode, from `dirichletSine_iteratedDeriv_two`:
`∂ₓₓ heatMode = -λₖ heatMode`. -/
lemma iteratedDeriv_two_heatMode (D : ℝ) (k : ℕ+) (t x : ℝ) :
    iteratedDeriv 2 (heatMode D k t) x = -dirichletLaplacianEigenvalue k * heatMode D k t x := by
  have hd : Differentiable ℝ (deriv (sineBasisFun k)) := by
    simpa [iteratedDeriv_one] using
      (dirichletSine_contDiff k).differentiable_iteratedDeriv 1 (by simp)
  have h1 : deriv (heatMode D k t) =
      fun y => Real.exp (-D * dirichletLaplacianEigenvalue k * t) * deriv (sineBasisFun k) y :=
    funext fun y => (hasDerivAt_heatMode_space D k t y).deriv
  have h2 := dirichletSine_iteratedDeriv_two k x
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, deriv_const_mul _ (hd x), h2, heatMode]
  ring

/-- Heat modes are smooth in `(t, x)`. -/
lemma contDiff_heatMode (D : ℝ) (k : ℕ+) : ContDiff ℝ ⊤ (Function.uncurry (heatMode D k)) :=
  ((contDiff_const.mul contDiff_fst).exp).mul ((dirichletSine_contDiff k).comp contDiff_snd)

/-- **Heat modes solve the heat equation** (MF08.3): `∂ₜu = D ∂ₓₓu` at every `(t, x)`, for
every real `D` (in particular `D > 0`). -/
lemma heatMode_heatEquation (D : ℝ) (k : ℕ+) (t x : ℝ) :
    deriv (fun τ => heatMode D k τ x) t = D * iteratedDeriv 2 (heatMode D k t) x := by
  rw [(hasDerivAt_heatMode_time D k t x).deriv, iteratedDeriv_two_heatMode]
  ring

/-- Left Dirichlet value of a heat mode: `u t 0 = 0`, from `dirichletSine_zero`. -/
lemma heatMode_space_zero (D : ℝ) (k : ℕ+) (t : ℝ) : heatMode D k t 0 = 0 := by
  rw [heatMode, dirichletSine_zero, mul_zero]

/-- Right Dirichlet value of a heat mode: `u t 1 = 0`, from `dirichletSine_one`. -/
lemma heatMode_space_one (D : ℝ) (k : ℕ+) (t : ℝ) : heatMode D k t 1 = 0 := by
  rw [heatMode, dirichletSine_one, mul_zero]

/-- Initial data of a heat mode: `u 0 x = sineBasisFun k x`. -/
lemma heatMode_time_zero (D : ℝ) (k : ℕ+) (x : ℝ) : heatMode D k 0 x = sineBasisFun k x := by
  rw [heatMode, mul_zero, Real.exp_zero, one_mul]

/-!

## D. Energy decay and uniqueness for the Dirichlet heat equation

The solution class of this section: `u : ℝ → ℝ → ℝ` (time, then space) is jointly `C²` on
`ℝ × ℝ`, that is `ContDiff ℝ 2 (Function.uncurry u)`; in particular `u` is `C¹` in `t` and `C²`
in `x` with continuous derivatives. The heat equation `∂ₜu = D ∂ₓₓu` and the Dirichlet values
`u t 0 = u t L = 0` are imposed only at the times stated in each result, and only on `[0, L]`.

-/

/-- **Oriented heat-energy integral** (MF08.4): `E(t) = ∫₀ᴸ u(t, x)² dx`.
For `0 ≤ L` this is the energy on `[0, L]`; for `L < 0` it is a signed integral,
not a nonnegative energy. -/
noncomputable def heatEnergy (L : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, u t x ^ 2

/-- The heat energy is nonnegative. -/
lemma heatEnergy_nonneg {L : ℝ} (hL : 0 ≤ L) (u : ℝ → ℝ → ℝ) (t : ℝ) : 0 ≤ heatEnergy L u t :=
  intervalIntegral.integral_nonneg hL fun _ _ => sq_nonneg _

/-- **Energy identity** (MF08.4): if `u` is jointly `C²`, solves `∂ₜu = D ∂ₓₓu` on `[0, L]` at
time `t` and vanishes at `x = 0` and `x = L` at time `t`, then
`E'(t) = -2D ∫₀ᴸ (∂ₓu)²`. The proof applies `hasDerivAt_integral_of_localConservation` to the
density `u²`, the flux `-2D u ∂ₓu` and the source `-2D (∂ₓu)²`; the boundary terms vanish by
the Dirichlet condition. -/
lemma hasDerivAt_heatEnergy {D L : ℝ} {u : ℝ → ℝ → ℝ} {t : ℝ} (hL : 0 ≤ L)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hheat : ∀ x ∈ Icc 0 L, deriv (fun τ => u τ x) t = D * iteratedDeriv 2 (u t) x)
    (hleft : u t 0 = 0) (hright : u t L = 0) :
    HasDerivAt (heatEnergy L u) (-2 * D * ∫ x in (0 : ℝ)..L, deriv (u t) x ^ 2) t := by
  have hu1 : ContDiff ℝ 1 (Function.uncurry u) := hu.of_le (by norm_num)
  set ux : ℝ → ℝ → ℝ := fun τ x => fderiv ℝ (Function.uncurry u) (τ, x) (0, 1)
  have hux (τ x : ℝ) : HasDerivAt (u τ) (ux τ x) x := hasDerivAt_snd_of_contDiff hu1 τ x
  have hux1 : ContDiff ℝ 1 (Function.uncurry ux) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have huxx (x : ℝ) : HasDerivAt (ux t) (fderiv ℝ (Function.uncurry ux) (t, x) (0, 1)) x :=
    hasDerivAt_snd_of_contDiff hux1 t x
  set q : ℝ → ℝ → ℝ := fun τ x => -(2 * D * (u τ x * ux τ x)) with hq
  set s : ℝ → ℝ → ℝ := fun τ x => -(2 * D * ux τ x ^ 2) with hs
  have he1 : ContDiff ℝ 1 (Function.uncurry fun τ x => u τ x ^ 2) := hu1.pow 2
  have hq1 : ContDiff ℝ 1 (Function.uncurry q) := (contDiff_const.mul (hu1.mul hux1)).neg
  have hlaw : ∀ x ∈ uIcc 0 L, localConservation (fun τ x => u τ x ^ 2) q s t x := by
    intro x hx
    rw [uIcc_of_le hL] at hx
    have ht := hasDerivAt_fst_of_contDiff hu1 t x
    have hxx : iteratedDeriv 2 (u t) x = fderiv ℝ (Function.uncurry ux) (t, x) (0, 1) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one,
        show deriv (u t) = ux t from funext fun y => (hux t y).deriv, (huxx x).deriv]
    have hpde := hheat x hx
    rw [ht.deriv, hxx] at hpde
    have hsq : HasDerivAt (fun τ => u τ x ^ 2)
        (2 * u t x * fderiv ℝ (Function.uncurry u) (t, x) (1, 0)) t := by
      simpa using ht.fun_pow 2
    have hqx : HasDerivAt (q t) (-(2 * D * (ux t x * ux t x +
        u t x * fderiv ℝ (Function.uncurry ux) (t, x) (0, 1)))) x :=
      (((hux t x).fun_mul (huxx x)).const_mul (2 * D)).neg
    rw [localConservation, hsq.deriv, hqx.deriv, hpde]
    simp only [hs]
    ring
  have hmain := hasDerivAt_integral_of_localConservation he1 hq1 hlaw
  have hval : integralBalance q s 0 L t = -2 * D * ∫ x in (0 : ℝ)..L, deriv (u t) x ^ 2 := by
    have hux' (x : ℝ) : ux t x = deriv (u t) x := (hux t x).deriv.symm
    simp only [integralBalance, hq, hs, hleft, hright, hux', zero_mul, mul_zero, neg_zero,
      sub_zero, zero_add, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    ring
  rw [hval] at hmain
  exact hmain

/-- **Energy dissipation** (MF08.4): under the hypotheses of `hasDerivAt_heatEnergy` with
`D ≥ 0`, the heat energy has nonpositive time derivative at `t`. -/
lemma deriv_heatEnergy_nonpos {D L : ℝ} {u : ℝ → ℝ → ℝ} {t : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hheat : ∀ x ∈ Icc 0 L, deriv (fun τ => u τ x) t = D * iteratedDeriv 2 (u t) x)
    (hleft : u t 0 = 0) (hright : u t L = 0) :
    deriv (heatEnergy L u) t ≤ 0 := by
  rw [(hasDerivAt_heatEnergy hL hu hheat hleft hright).deriv]
  have h : 0 ≤ ∫ x in (0 : ℝ)..L, deriv (u t) x ^ 2 :=
    intervalIntegral.integral_nonneg hL fun x _ => sq_nonneg (deriv (u t) x)
  nlinarith [mul_nonneg hD h]

/-- **Energy decay** (MF08.4): a jointly `C²` solution of `∂ₜu = D ∂ₓₓu` (`D ≥ 0`) on `[0, L]`
with zero Dirichlet values for `t ≥ 0` has nonincreasing heat energy on `t ≥ 0`. -/
lemma antitoneOn_heatEnergy {D L : ℝ} {u : ℝ → ℝ → ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hheat : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 L, deriv (fun τ => u τ x) t = D * iteratedDeriv 2 (u t) x)
    (hleft : ∀ t, 0 ≤ t → u t 0 = 0) (hright : ∀ t, 0 ≤ t → u t L = 0) :
    AntitoneOn (heatEnergy L u) (Ici 0) := by
  have hcont : Continuous (heatEnergy L u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (hu.continuous.pow 2) 0 L
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn (fun t ht => ?_)
    fun t ht => ?_
  · rw [interior_Ici] at ht
    exact (hasDerivAt_heatEnergy hL hu (hheat t ht.le) (hleft t ht.le)
      (hright t ht.le)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at ht
    exact deriv_heatEnergy_nonpos hD hL hu (hheat t ht.le) (hleft t ht.le) (hright t ht.le)

/-- **Uniqueness for the Dirichlet heat equation** (MF08.4, energy method). Let `u` and `v` be
jointly `C²` solutions of `∂ₜu = D ∂ₓₓu` (`D ≥ 0`) on `[0, L]` (`L > 0`) with zero Dirichlet
values for `t ≥ 0`. If `u 0 = v 0` on `[0, L]`, then `u t x = v t x` for all `t ≥ 0` and
`x ∈ [0, L]`. The energy of `u - v` is nonnegative, nonincreasing and zero at `t = 0`. -/
theorem heatEquation_unique {D L : ℝ} {u v : ℝ → ℝ → ℝ} (hD : 0 ≤ D) (hL : 0 < L)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (hv : ContDiff ℝ 2 (Function.uncurry v))
    (hu_heat : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 L,
      deriv (fun τ => u τ x) t = D * iteratedDeriv 2 (u t) x)
    (hv_heat : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 L,
      deriv (fun τ => v τ x) t = D * iteratedDeriv 2 (v t) x)
    (hu_left : ∀ t, 0 ≤ t → u t 0 = 0) (hu_right : ∀ t, 0 ≤ t → u t L = 0)
    (hv_left : ∀ t, 0 ≤ t → v t 0 = 0) (hv_right : ∀ t, 0 ≤ t → v t L = 0)
    (hinit : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : x ∈ Icc 0 L) :
    u t x = v t x := by
  set w : ℝ → ℝ → ℝ := fun τ y => u τ y - v τ y with hw_def
  have hw : ContDiff ℝ 2 (Function.uncurry w) := hu.sub hv
  have hw_heat : ∀ t, 0 ≤ t → ∀ x ∈ Icc 0 L,
      deriv (fun τ => w τ x) t = D * iteratedDeriv 2 (w t) x := by
    intro τ hτ y hy
    have hut := hasDerivAt_fst_of_contDiff (hu.of_le (by norm_num)) τ y
    have hvt := hasDerivAt_fst_of_contDiff (hv.of_le (by norm_num)) τ y
    have hu2 : ContDiff ℝ 2 (u τ) := hu.comp (contDiff_const.prodMk contDiff_id)
    have hv2 : ContDiff ℝ 2 (v τ) := hv.comp (contDiff_const.prodMk contDiff_id)
    rw [hw_def, deriv_fun_sub hut.differentiableAt hvt.differentiableAt,
      iteratedDeriv_fun_sub (by exact_mod_cast hu2.contDiffAt)
        (by exact_mod_cast hv2.contDiffAt), hu_heat τ hτ y hy, hv_heat τ hτ y hy]
    ring
  have hE := antitoneOn_heatEnergy hD hL.le hw hw_heat
    (fun τ hτ => by simp [hw_def, hu_left τ hτ, hv_left τ hτ])
    (fun τ hτ => by simp [hw_def, hu_right τ hτ, hv_right τ hτ])
  have hE0 : heatEnergy L w 0 = 0 := by
    rw [heatEnergy, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun y hy => by
      rw [uIcc_of_le hL.le] at hy
      simp [hw_def, hinit y hy]]
    simp
  have hEt : heatEnergy L w t = 0 :=
    le_antisymm (hE0 ▸ hE self_mem_Ici ht ht) (heatEnergy_nonneg hL.le w t)
  by_contra hne
  have hwx : w t x ≠ 0 := sub_ne_zero.2 hne
  have hpos : 0 < heatEnergy L w t :=
    intervalIntegral.integral_pos hL
      ((hw.continuous.comp (continuous_const.prodMk continuous_id)).pow 2).continuousOn
      (fun _ _ => sq_nonneg _) ⟨x, hx, by positivity⟩
  linarith

end MathlibExt.Analysis.ODE.ContinuumBalances
