/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.Order.Field
import PhyslibExt.EarthScience.PointRelease

/-!

# Continuum diffusion in one dimension (Fick's laws)

Fick's first law, the diffusion equation it gives together with the continuity equation, and its
classical solutions: the Gaussian on the line, the complementary-error-function profile on the
half-line, the steady membrane profile and the sine series for a slab, with uniqueness for the
Dirichlet problem by the energy method.

## i. Overview

All quantities are real numbers after a consistent choice of units; dimensions are not tracked.
A concentration field is a function `c : ℝ → ℝ → ℝ` of the position `x` and then the time `t`,
and the diffusivity `D` is a real constant; the results assume `0 < D` where they need it.
Partial derivatives are Mathlib `deriv`s of the partial maps or are given by explicit
`HasDerivAt` hypotheses. Since `deriv` is `0` where a map is not differentiable, a statement
written with `deriv` carries meaning together with the differentiability results or hypotheses
stated beside it.

* Fick's first law (A). The flux is `J = -D ∂ₓc` (`fickFlux`). Together with the continuity
  equation `∂ₜc + ∂ₓJ = 0` it gives the diffusion equation `∂ₜc = D ∂ₓₓc`; Fick's law alone does
  not. The divergence form `∂ₜu = ∂ₓ(D ∂ₓu) + s` for a variable diffusivity is
  `MathlibExt.Analysis.ODE.ContinuumBalances.localConservation_diffusiveFlux_iff`.
* Gaussian (B). For `D > 0` and `t > 0`, `gauss M D x t = M / √(4πDt) · exp(-x² / (4Dt))`
  solves the diffusion equation and has total mass `M` on the line, for every real `M`. It is
  the point-release kernel of `PhyslibExt.EarthScience.PointRelease` with no drift and no
  reaction, and `gauss_pde` and `gauss_mass` are derived from
  `EarthScience.point_release_solves_adr` and `EarthScience.point_release_integral`. For
  `M > 0` the Gaussian tends to the point mass `M δ₀` as `t → 0⁺`:
  `∫ gauss M D x t · φ x dx → M φ(0)` for every bounded continuous `φ`.
* Error-function profile (C). `erfc x = 1 - (2/√π) ∫₀ˣ exp(-s²) ds` is defined here, since the
  pinned Mathlib has no error function. For `D > 0` and `t > 0`,
  `erfcProfile cs D x t = cs · erfc(x / √(4Dt))` solves the diffusion equation, equals `cs` at
  `x = 0` and tends to `0` as `x → ∞`; for each `x > 0` it tends to `0` as `t → 0⁺`. For
  `cs > 0` the amount `∫₀^∞ erfcProfile cs D x t dx` is strictly increasing in `t > 0`: the
  surface supplies mass. Its closed form `2 cs √(Dt/π)` is not proved.
* Dirichlet uniqueness (D). Let `w = c₁ - c₂` be continuous on the closed rectangle
  `[a, b] × [0, T]`, let its derivatives `∂ₓw`, `∂ₓₓw`, `∂ₜw` be continuous on `[a, b] × (0, T)`,
  and let `w` solve `∂ₜw = D ∂ₓₓw` at the points of `(a, b) × (0, T)` and vanish at `x = a` and
  `x = b` for `0 < t < T` and at `t = 0`. Then `c₁ = c₂` on the rectangle: the energy
  `E(t) = ∫ₐᵇ w² dx` is continuous on `[0, T]` with `E'(t) = -2D ∫ₐᵇ (∂ₓw)² ≤ 0` on `(0, T)`.
  Nothing is assumed outside the rectangle, so the result applies to solutions that exist only
  up to time `T`. `MathlibExt.Analysis.ODE.ContinuumBalances.heatEquation_unique` assumes
  instead solutions that are jointly `C²` on all of `ℝ × ℝ`.
* Parabolic scaling (E). If `c` solves the diffusion equation at `(λx, λ²t)`, with its spatial
  derivative given along the whole line at time `λ²t`, then `(x, t) ↦ c(λx, λ²t)` solves it at
  `(x, t)`; in particular a solution on all of `ℝ × ℝ` rescales to one. The similarity variable
  `x / √(Dt)` is invariant under this scaling.
* Steady membrane (F). For `L > 0`, the linear profile from `c₁` at `x = 0` to `c₂` at `x = L`
  solves the steady equation, and its flux is `D (c₁ - c₂) / L` at every `x`. The linear
  interpolant on a general interval `[a, b]` is treated in
  `MathlibExt.Analysis.ODE.ContinuumBalances` (`linear_solves_steady`,
  `eq_linear_of_hasDerivAt_zero`); here the profile is used for the membrane flux.
* Slab series (G). For the uniform initial concentration `c₀` on `[0, L]`, the sine coefficients
  are `bₙ = 2c₀ (1 - (-1)ⁿ) / (nπ)`: `4c₀ / (nπ)` for odd `n` and `0` for even `n`. For `c₀ ≥ 0`
  the series `∑ bₙ sin(nπx/L) exp(-D (nπ/L)² t)` converges uniformly on `[0, L] × [δ, ∞)` for
  every `δ > 0`. That its sum solves the diffusion equation or attains the initial data is not
  proved.

Not covered: existence for general data, concentration-dependent diffusivity, several components
or cross-diffusion, and dimensional quantities.

## ii. Key results

- `fickFlux`, `fick_continuity_imply_diffusion` : Fick's first law and the diffusion equation.
- `gauss`, `gauss_pde`, `gauss_mass` : the Gaussian solves the diffusion equation and conserves
  mass.
- `gauss_weak_limit` : for `M > 0` the Gaussian tends to the point mass `M δ₀` as `t → 0⁺`.
- `erfc`, `erfcProfile`, `erfcProfile_pde` : the error-function profile solves the diffusion
  equation.
- `erfcProfile_surface`, `erfcProfile_farfield`, `erfcProfile_initial` : its surface value,
  far-field limit and initial limit.
- `erfcProfile_mass_strictMono` : the amount that has entered the half-line increases with time.
- `energy_identity_deriv`, `diffusion_unique_dirichlet` : the energy identity at interior times
  and uniqueness for the Dirichlet problem on a finite time interval.
- `scaledSol`, `similarity_pde_at`, `similarity_pde`, `simVar_invariant` : parabolic scaling.
- `steadyProfile`, `steady_pde`, `steady_flux` : the steady membrane profile and its flux.
- `fourierCoeff`, `fourierTerm`, `fourierCoeff_formula`, `fourier_uniform_convergent` : the slab
  sine series, its coefficients and its uniform convergence for positive times.

## iii. Table of contents

- A. Fick's first law and the diffusion equation
- B. The Gaussian on the line
  - B.1. Derivatives and the diffusion equation
  - B.2. Mass and the initial limit
- C. The complementary error function profile
  - C.1. The complementary error function
  - C.2. The profile and the diffusion equation
  - C.3. Surface, far-field and initial values
  - C.4. Mass uptake through the surface
- D. Uniqueness for the Dirichlet problem
- E. Parabolic scaling
- F. The steady membrane profile
- G. The slab sine series

## iv. References

- J. Crank, *The Mathematics of Diffusion*, 2nd ed., Clarendon Press, Oxford, 1975, Chapters 1–4
  (Fick's laws; solutions for a constant diffusion coefficient in infinite and semi-infinite
  media and in a plane sheet).
- R. W. Balluffi, S. M. Allen and W. C. Carter, *Kinetics of Materials*, Wiley, 2005, Chapters 4
  and 5 (the diffusion equation and its solutions).
- L. C. Evans, *Partial Differential Equations*, 2nd ed., American Mathematical Society, 2010,
  §2.3 (the heat equation: fundamental solution, and uniqueness by the energy method).

-/

open MeasureTheory Set Filter Topology Real

open scoped intervalIntegral Interval

@[expose] public section

namespace CondensedMatter.Diffusion

/-!

## A. Fick's first law and the diffusion equation

-/

/-- **Fick's first law** in one dimension with constant diffusivity `D`: the flux of the
concentration field `c` (position, then time) at `(x, t)` is `J = -D ∂ₓc(x, t)`. The derivative
is Mathlib's `deriv`, which is `0` where `c (·) t` is not differentiable at `x`, so results about
`fickFlux` assume that differentiability separately. -/
noncomputable def fickFlux (D : ℝ) (c : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  -D * deriv (fun x' => c x' t) x

/-- **Fick's second law from the continuity equation.** Suppose the concentration `c` has the
time derivative `ct'` at `(x, t)`, its spatial derivative `∂ₓc(·, t)` has the derivative `cxx'`
at `x`, and the continuity equation `∂ₜc + ∂ₓJ = 0` holds at `(x, t)` for the Fick flux
`J = fickFlux D c` (hypothesis `Hcont`). Then `∂ₜc = D cxx'` at `(x, t)`. Fick's law alone does
not give this conclusion. -/
theorem fick_continuity_imply_diffusion (D : ℝ) (c : ℝ → ℝ → ℝ) (x t cxx' ct' : ℝ)
    (H2 : HasDerivAt (fun x' => deriv (fun x'' => c x'' t) x') cxx' x)
    (Ht : HasDerivAt (fun t' => c x t') ct' t)
    (Hcont : ct' + deriv (fun x' => fickFlux D c x' t) x = 0) :
    deriv (fun t' => c x t') t = D * cxx' := by
  have hJ : deriv (fun x' => fickFlux D c x' t) x = -D * cxx' :=
    (H2.const_mul (-D)).deriv
  rw [Ht.deriv]
  rw [hJ] at Hcont
  linarith

/-!

## B. The Gaussian on the line

-/

/-- The Gaussian solution on the line with total mass `M`:
`gauss M D x t = M / √(4πDt) · exp(-x² / (4Dt))`. It is meant for `D > 0` and `t > 0`. For
`D > 0` and `t ≤ 0` the square root is `0` and Lean's convention `M / 0 = 0` makes the value `0`.
It is the point-release kernel of `PhyslibExt.EarthScience.PointRelease` with no drift and no
reaction. -/
noncomputable def gauss (M D x t : ℝ) : ℝ :=
  (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-x ^ 2 / (4 * D * t))

/-!

### B.1. Derivatives and the diffusion equation

-/

/-- The spatial derivative of the Gaussian for `D > 0` and `t > 0`:
`∂ₓ gauss = gauss · (-x / (2Dt))`. -/
lemma gauss_xderiv_value (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => gauss M D x t) (gauss M D x t * (-x / (2 * D * t))) x := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hs : (4 * D * t : ℝ) ≠ 0 := by positivity
  have hs2 : (2 * D * t : ℝ) ≠ 0 := by positivity
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hu : HasDerivAt (fun x : ℝ => -x ^ 2 / (4 * D * t)) (-(2 * x) / (4 * D * t)) x :=
    hpow.neg.div_const _
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / (4 * D * t)))
      (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t))) x := by
    simpa using hu.exp
  have hraw : HasDerivAt (fun x : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) *
      Real.exp (-x ^ 2 / (4 * D * t)))
      ((M / Real.sqrt (4 * Real.pi * D * t)) *
        (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t)))) x := by
    simpa using hexp.const_mul _
  have hval : ((M / Real.sqrt (4 * Real.pi * D * t)) *
      (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t))))
      = gauss M D x t * (-x / (2 * D * t)) := by
    simp only [gauss]
    field_simp
    ring
  rwa [hval] at hraw

/-- The second spatial derivative of the Gaussian for `D > 0` and `t > 0`:
`∂ₓₓ gauss = gauss · (x² / (4D²t²) - 1 / (2Dt))`. -/
lemma gauss_xxderiv_value (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => deriv (fun x' => gauss M D x' t) x)
      (gauss M D x t * (x ^ 2 / (4 * D ^ 2 * t ^ 2) - 1 / (2 * D * t))) x := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have hs2 : (2 * D * t : ℝ) ≠ 0 := by positivity
  have h4D2t2 : (4 * D ^ 2 * t ^ 2 : ℝ) ≠ 0 := by positivity
  have hfun : (fun x => deriv (fun x' => gauss M D x' t) x)
      = (fun x => gauss M D x t * (-x / (2 * D * t))) := by
    funext x'
    exact (gauss_xderiv_value M D x' t hD ht).deriv
  rw [hfun]
  have hlin : HasDerivAt (fun x : ℝ => -x / (2 * D * t)) (-1 / (2 * D * t)) x := by
    simpa using (hasDerivAt_id' x).neg.div_const _
  have hmul : HasDerivAt (fun x : ℝ => gauss M D x t * (-x / (2 * D * t)))
      ((gauss M D x t * (-x / (2 * D * t))) * (-x / (2 * D * t))
        + gauss M D x t * (-1 / (2 * D * t))) x := by
    convert (gauss_xderiv_value M D x t hD ht).mul hlin using 1
  have hval : ((gauss M D x t * (-x / (2 * D * t))) * (-x / (2 * D * t))
      + gauss M D x t * (-1 / (2 * D * t)))
      = gauss M D x t * (x ^ 2 / (4 * D ^ 2 * t ^ 2) - 1 / (2 * D * t)) := by
    field_simp
    ring
  rwa [hval] at hmul

/-- The time derivative of the Gaussian for `D > 0` and `t > 0`:
`∂ₜ gauss = gauss · (x² / (4Dt²) - 1 / (2t))`. -/
lemma gauss_tderiv_value (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun t => gauss M D x t)
      (gauss M D x t * (x ^ 2 / (4 * D * t ^ 2) - 1 / (2 * t))) t := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have hQ' : (4 * Real.pi * D * t : ℝ) ≠ 0 := ne_of_gt hQ
  have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hden : HasDerivAt (fun t : ℝ => 4 * D * t) (4 * D) t := by
    simpa using (hasDerivAt_id' t).const_mul (4 * D)
  have hden' : (4 * D * t : ℝ) ≠ 0 := by positivity
  have hden2 : (4 * D * t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hden'
  have h2t : (2 * t : ℝ) ≠ 0 := by positivity
  have h4Dt2 : (4 * D * t ^ 2 : ℝ) ≠ 0 := by positivity
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht'
  have hS : HasDerivAt (fun t : ℝ => 4 * Real.pi * D * t) (4 * Real.pi * D) t := by
    simpa using (hasDerivAt_id' t).const_mul (4 * Real.pi * D)
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (4 * Real.pi * D * t))
      ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))) t :=
    hS.sqrt hQ'
  have hA : HasDerivAt (fun t : ℝ => M / Real.sqrt (4 * Real.pi * D * t))
      ((0 * Real.sqrt (4 * Real.pi * D * t)
        - M * ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))))
        / (Real.sqrt (4 * Real.pi * D * t)) ^ 2) t := by
    convert (hasDerivAt_const t M).div hsqrt hsq using 1
  have hexp_arg : HasDerivAt (fun t : ℝ => -x ^ 2 / (4 * D * t))
      ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2) t := by
    convert (hasDerivAt_const t (-x ^ 2)).div hden hden' using 1
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-x ^ 2 / (4 * D * t)))
      (Real.exp (-x ^ 2 / (4 * D * t))
        * ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2)) t := by
    simpa using hexp_arg.exp
  have hmul : HasDerivAt (fun t : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) *
      Real.exp (-x ^ 2 / (4 * D * t)))
      (((0 * Real.sqrt (4 * Real.pi * D * t)
        - M * ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))))
        / (Real.sqrt (4 * Real.pi * D * t)) ^ 2) * Real.exp (-x ^ 2 / (4 * D * t))
        + (M / Real.sqrt (4 * Real.pi * D * t)) * (Real.exp (-x ^ 2 / (4 * D * t))
        * ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2))) t := by
    convert hA.mul hE using 1
  have hsqrt_inv : (Real.sqrt (4 * Real.pi * D * t))⁻¹
      = Real.sqrt (4 * Real.pi * D * t) / (4 * Real.pi * D * t) := by
    have hmul2 : Real.sqrt (4 * Real.pi * D * t) * Real.sqrt (4 * Real.pi * D * t)
        = 4 * Real.pi * D * t := by
      rw [← sq, Real.sq_sqrt hQ.le]
    rw [eq_div_iff hQ']
    calc (Real.sqrt (4 * Real.pi * D * t))⁻¹ * (4 * Real.pi * D * t)
        = (Real.sqrt (4 * Real.pi * D * t))⁻¹
          * (Real.sqrt (4 * Real.pi * D * t) * Real.sqrt (4 * Real.pi * D * t)) := by
          rw [hmul2]
      _ = Real.sqrt (4 * Real.pi * D * t) := by
          rw [← mul_assoc, inv_mul_cancel₀ hsq, one_mul]
  have hval : (((0 * Real.sqrt (4 * Real.pi * D * t)
      - M * ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))))
      / (Real.sqrt (4 * Real.pi * D * t)) ^ 2) * Real.exp (-x ^ 2 / (4 * D * t))
      + (M / Real.sqrt (4 * Real.pi * D * t)) * (Real.exp (-x ^ 2 / (4 * D * t))
      * ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2)))
      = gauss M D x t * (x ^ 2 / (4 * D * t ^ 2) - 1 / (2 * t)) := by
    simp only [gauss]
    rw [Real.sq_sqrt hQ.le]
    simp only [div_eq_mul_inv, mul_inv]
    rw [hsqrt_inv]
    field_simp
    ring
  have hgauss_eq : (fun t : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) *
      Real.exp (-x ^ 2 / (4 * D * t))) = (fun t => gauss M D x t) := by
    funext t
    rfl
  rw [hval, hgauss_eq] at hmul
  exact hmul

/-- The point-release kernel with no drift and no reaction is the Gaussian. -/
private lemma pointRelease_zero_eq (M D t x : ℝ) :
    M * Real.exp (-0 * t) * Real.exp (-(x - 0 * t) ^ 2 / (4 * D * t)) /
      Real.sqrt (4 * Real.pi * D * t) = gauss M D x t := by
  simp only [gauss, neg_zero, zero_mul, Real.exp_zero, mul_one, sub_zero]
  ring

/-- **The Gaussian solves the diffusion equation.** For `D > 0`, `t > 0` and every real `M`
and `x`, `∂ₜ gauss = D ∂ₓₓ gauss` at `(x, t)`. This is `EarthScience.point_release_solves_adr`
with no drift and no reaction; the derivatives exist by `gauss_tderiv_value` and
`gauss_xxderiv_value`. -/
theorem gauss_pde (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun t => gauss M D x t) t
      = D * deriv (fun x => deriv (fun x' => gauss M D x' t) x) x := by
  have hx' : (fun x' => M * Real.exp (-0 * t) * Real.exp (-(x' - 0 * t) ^ 2 / (4 * D * t)) /
      Real.sqrt (4 * Real.pi * D * t)) = fun x' => gauss M D x' t :=
    funext fun x' => pointRelease_zero_eq M D t x'
  have ht' : (fun t => M * Real.exp (-0 * t) * Real.exp (-(x - 0 * t) ^ 2 / (4 * D * t)) /
      Real.sqrt (4 * Real.pi * D * t)) = fun t => gauss M D x t :=
    funext fun t => pointRelease_zero_eq M D t x
  have h := EarthScience.point_release_solves_adr M D 0 0 t x hD ht
  rw [ht', hx'] at h
  simpa only [zero_mul, add_zero, sub_zero] using h

/-!

### B.2. Mass and the initial limit

-/

/-- The Gaussian is nonnegative for `M > 0`, `D > 0` and `t > 0`. -/
lemma gauss_nonneg (M D x t : ℝ) (hM : 0 < M) (hD : 0 < D) (ht : 0 < t) :
    0 ≤ gauss M D x t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have h1 : (0 : ℝ) ≤ M / Real.sqrt (4 * Real.pi * D * t) :=
    div_nonneg hM.le (Real.sqrt_pos.mpr hQ).le
  have h2 : (0 : ℝ) ≤ Real.exp (-x ^ 2 / (4 * D * t)) := (Real.exp_pos _).le
  simp only [gauss]
  exact mul_nonneg h1 h2

/-- **Conservation of mass.** For `D > 0`, `t > 0` and every real `M`, the Gaussian has total
mass `∫ gauss M D x t dx = M` on the line. This is `EarthScience.point_release_integral` with no
drift and no reaction. -/
theorem gauss_mass (M D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    ∫ x, gauss M D x t = M := by
  have hx' : (fun x => M * Real.exp (-0 * t) * Real.exp (-(x - 0 * t) ^ 2 / (4 * D * t)) /
      Real.sqrt (4 * Real.pi * D * t)) = fun x => gauss M D x t :=
    funext fun x => pointRelease_zero_eq M D t x
  have h := EarthScience.point_release_integral M D 0 0 t hD ht
  rw [hx'] at h
  simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using h

/-- **Initial limit of the Gaussian.** For `0 < M`, `D > 0` and a bounded continuous `φ`,
`∫ gauss M D x t · φ x dx → M φ(0)` as `t → 0⁺`: the Gaussian tends to the point mass `M δ₀`.
The statement assumes `0 < M`, which the proof uses (the Gaussian is then nonnegative); the case
`M ≤ 0` is not covered. -/
theorem gauss_weak_limit (M D : ℝ) (hM : 0 < M) (hD : 0 < D) (φ : ℝ → ℝ)
    (hφc : Continuous φ) (hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    Tendsto (fun t => ∫ x, gauss M D x t * φ x) (𝓝[>] (0 : ℝ)) (𝓝 (M * φ 0)) := by
  obtain ⟨C, hC⟩ := hφb
  have hM' : M ≠ 0 := ne_of_gt hM
  have hD' : D ≠ 0 := ne_of_gt hD
  have hC' : ∀ x, |φ x| ≤ |C| + 1 := fun x => le_trans (hC x) (by
    calc C ≤ |C| := le_abs_self C
    _ ≤ |C| + 1 := by linarith)
  have hKint : ∀ (t : ℝ) (ht : 0 < t),
      Integrable (fun x => Real.exp (-(1 / (4 * D * t)) * x ^ 2)) := by
    intro t ht
    apply integrable_exp_neg_mul_sq
    positivity
  have hKt : ∀ (t : ℝ) (ht : 0 < t), Integrable (fun x => gauss M D x t) := by
    intro t ht
    have h4Dt : (4 * D * t : ℝ) ≠ 0 := by positivity
    have hker : ∀ x : ℝ, gauss M D x t
        = (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-(1 / (4 * D * t)) * x ^ 2) := by
      intro x
      simp only [gauss]
      have he : (-x ^ 2 / (4 * D * t)) = (-(1 / (4 * D * t)) * x ^ 2) := by
        field_simp
      rw [he]
    simp_rw [hker]
    simpa [smul_eq_mul] using (hKint t ht).const_mul _
  have hφ0K : ∀ (t : ℝ) (ht : 0 < t), Integrable (fun x => φ 0 * gauss M D x t) := by
    intro t ht
    simpa [smul_eq_mul] using (hKt t ht).const_mul _
  have hφKt : ∀ (t : ℝ) (ht : 0 < t), Integrable (fun x => gauss M D x t * φ x) := by
    intro t ht
    have hmeas : AEStronglyMeasurable φ volume := hφc.aestronglyMeasurable
    have hbdd : ∀ᵐ x ∂volume, ‖φ x‖ ≤ |C| + 1 := by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hC' x
    have h : Integrable (fun x => φ x • gauss M D x t) := (hKt t ht).bdd_mul hmeas hbdd
    have heq : (fun x => φ x • gauss M D x t) = (fun x => gauss M D x t * φ x) := by
      funext x
      rw [smul_eq_mul, mul_comm]
    rwa [heq] at h
  have hfullint : ∀ (t : ℝ) (ht : 0 < t),
      Integrable (fun x => gauss M D x t * (φ x - φ 0)) := by
    intro t ht
    have h1 := hφKt t ht
    have h2 := hφ0K t ht
    have hsub : Integrable (fun x : ℝ => gauss M D x t * φ x - φ 0 * gauss M D x t) :=
      h1.sub h2
    have heq : (fun x : ℝ => gauss M D x t * φ x - φ 0 * gauss M D x t)
        = (fun x => gauss M D x t * (φ x - φ 0)) := by
      funext x
      ring
    rwa [heq] at hsub
  have hmass : ∀ (t : ℝ) (ht : 0 < t), ∫ x, gauss M D x t = M :=
    fun t ht => gauss_mass M D t hD ht
  have hdecomp : ∀ (t : ℝ) (ht : 0 < t),
      (∫ x, gauss M D x t * φ x) - M * φ 0
        = ∫ x, gauss M D x t * (φ x - φ 0) := by
    intro t ht
    have h1 := hφKt t ht
    have h2 := hφ0K t ht
    have hsub : (∫ x, gauss M D x t * φ x - φ 0 * gauss M D x t)
        = (∫ x, gauss M D x t * φ x) - ∫ x, φ 0 * gauss M D x t :=
      integral_sub h1 h2
    have hmassφ : (∫ x, φ 0 * gauss M D x t) = φ 0 * M := by
      have hsmul : (fun x : ℝ => φ 0 * gauss M D x t)
          = (fun x => φ 0 • gauss M D x t) := by
        funext x
        rw [smul_eq_mul]
      rw [hsmul, integral_smul, smul_eq_mul, hmass t ht]
    have hcongr : (∫ x, gauss M D x t * φ x - φ 0 * gauss M D x t)
        = ∫ x, gauss M D x t * (φ x - φ 0) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [← hcongr, hsub, hmassφ, mul_comm M (φ 0)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεM : (0 : ℝ) < ε / (2 * M) := by positivity
  have hcont0 : ContinuousAt φ 0 := hφc.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont0 (ε / (2 * M)) hεM
  have hsplit : ∀ (t : ℝ) (ht : 0 < t), (∫ x, gauss M D x t * (φ x - φ 0))
      = (∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))
        + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0) := by
    intro t ht
    exact (integral_add_compl measurableSet_Ioo (hfullint t ht)).symm
  have hnear : ∀ (t : ℝ) (ht : 0 < t),
      ‖(∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))‖ ≤ ε / 2 := by
    intro t ht
    have hpt : ∀ x ∈ Ioo (-δ) δ,
        ‖gauss M D x t * (φ x - φ 0)‖ ≤ gauss M D x t * (ε / (2 * M)) := by
      intro x hx
      have hxδ : |x| < δ := abs_lt.mpr (mem_Ioo.mp hx)
      have hdist : dist x 0 < δ := by
        rw [Real.dist_eq, sub_zero]
        exact hxδ
      have hφ := hδ hdist
      rw [Real.dist_eq] at hφ
      have hKnn : 0 ≤ gauss M D x t := gauss_nonneg M D x t hM hD ht
      calc ‖gauss M D x t * (φ x - φ 0)‖
          = |gauss M D x t| * |φ x - φ 0| := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ = gauss M D x t * |φ x - φ 0| := by rw [abs_of_nonneg hKnn]
        _ ≤ gauss M D x t * (ε / (2 * M)) :=
            mul_le_mul_of_nonneg_left (le_of_lt hφ) hKnn
    have hae : (fun x => ‖gauss M D x t * (φ x - φ 0)‖)
        ≤ᵐ[volume.restrict (Ioo (-δ) δ)]
        (fun x => gauss M D x t * (ε / (2 * M))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    have hInt : Integrable (fun x => gauss M D x t * (φ x - φ 0))
        (volume.restrict (Ioo (-δ) δ)) := (hfullint t ht).integrableOn
    have hnorm : IntegrableOn (fun x => ‖gauss M D x t * (φ x - φ 0)‖) (Ioo (-δ) δ) :=
      ((hfullint t ht).integrableOn : Integrable _ (volume.restrict (Ioo (-δ) δ))).norm
    have hconst : Integrable (fun x => gauss M D x t * (ε / (2 * M)))
        (volume.restrict (Ioo (-δ) δ)) := by
      have h := (((hKt t ht).integrableOn :
        Integrable _ (volume.restrict (Ioo (-δ) δ))).const_mul (ε / (2 * M)))
      have heq : (fun x : ℝ => (ε / (2 * M)) * gauss M D x t)
          = (fun x => gauss M D x t * (ε / (2 * M))) := by
        funext x
        ring
      simpa [smul_eq_mul, heq] using h
    have hpull : (∫ x in Ioo (-δ) δ, gauss M D x t * (ε / (2 * M)))
        = (ε / (2 * M)) * ∫ x in Ioo (-δ) δ, gauss M D x t := by
      have heq : (fun x : ℝ => gauss M D x t * (ε / (2 * M)))
          = (fun x => (ε / (2 * M)) • gauss M D x t) := by
        funext x
        rw [smul_eq_mul, mul_comm]
      rw [heq, integral_smul, smul_eq_mul]
    have hKle : (∫ x in Ioo (-δ) δ, gauss M D x t) ≤ M := by
      have hsp : (∫ x in Ioo (-δ) δ, gauss M D x t)
          + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t = ∫ x, gauss M D x t :=
        integral_add_compl measurableSet_Ioo (hKt t ht)
      have hnn : (0 : ℝ) ≤ ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t := by
        have hae0 : ∀ᵐ x ∂(volume.restrict ((Ioo (-δ) δ)ᶜ)),
            (0 : ℝ) ≤ gauss M D x t := by
          filter_upwards with x
          exact gauss_nonneg M D x t hM hD ht
        exact MeasureTheory.integral_nonneg_of_ae hae0
      rw [hmass t ht] at hsp
      linarith
    have hεMnn : (0 : ℝ) ≤ ε / (2 * M) := le_of_lt hεM
    calc ‖∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0)‖
        ≤ ∫ x in Ioo (-δ) δ, ‖gauss M D x t * (φ x - φ 0)‖ := by
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ x in Ioo (-δ) δ, gauss M D x t * (ε / (2 * M)) := by
          apply integral_mono_ae <;> assumption
      _ = (ε / (2 * M)) * ∫ x in Ioo (-δ) δ, gauss M D x t := hpull
      _ ≤ (ε / (2 * M)) * M := mul_le_mul_of_nonneg_left hKle hεMnn
      _ = ε / 2 := by
          field_simp
  have htail : ∀ (t : ℝ) (ht : 0 < t),
      (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t)
        ≤ M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
    intro t ht
    have hspos : (0 : ℝ) < 4 * D * t := by positivity
    have hs' : (4 * D * t : ℝ) ≠ 0 := ne_of_gt hspos
    have h2s' : (2 * (4 * D * t) : ℝ) ≠ 0 := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
    have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
    have hA : (0 : ℝ) ≤ M / Real.sqrt (4 * Real.pi * D * t) :=
      div_nonneg hM.le (Real.sqrt_pos.mpr hQ).le
    have hker2s : ∀ x : ℝ, (-x ^ 2 / (2 * (4 * D * t)))
        = (-(1 / (2 * (4 * D * t))) * x ^ 2) := by
      intro x
      field_simp
    have hb : (0 : ℝ) < 1 / (2 * (4 * D * t)) := by positivity
    have hbase : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
      simp_rw [hker2s]
      exact integrable_exp_neg_mul_sq hb
    have hpt : ∀ x ∈ (Ioo (-δ) δ)ᶜ, gauss M D x t
        ≤ (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
          * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      intro x hx
      simp only [Set.mem_compl_iff] at hx
      have hxδ : δ ≤ |x| := by
        by_contra hcon
        push Not at hcon
        exact hx (mem_Ioo.mpr (abs_lt.mp hcon))
      have hx2δ : δ ^ 2 ≤ x ^ 2 := by
        have h : δ ^ 2 ≤ |x| ^ 2 := by gcongr
        rwa [sq_abs x] at h
      have hexp_le : -x ^ 2 / (4 * D * t)
          ≤ (-δ ^ 2 + -x ^ 2) / (2 * (4 * D * t)) := by
        have h2s : (0 : ℝ) < 2 * (4 * D * t) := by positivity
        rw [le_div_iff₀ h2s]
        have hmul : (-x ^ 2 / (4 * D * t)) * (2 * (4 * D * t)) = -2 * x ^ 2 := by
          field_simp
        rw [hmul]
        linarith [hx2δ]
      have harg : -x ^ 2 / (4 * D * t)
          ≤ (-δ ^ 2 / (2 * (4 * D * t))) + (-x ^ 2 / (2 * (4 * D * t))) := by
        rw [← add_div]
        exact hexp_le
      have hexp_split : Real.exp (-x ^ 2 / (4 * D * t))
          ≤ Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
        calc Real.exp (-x ^ 2 / (4 * D * t))
            ≤ Real.exp ((-δ ^ 2 / (2 * (4 * D * t))) + (-x ^ 2 / (2 * (4 * D * t)))) :=
              Real.exp_le_exp.mpr harg
          _ = Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))) :=
              Real.exp_add _ _
      simp only [gauss]
      calc (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-x ^ 2 / (4 * D * t))
          ≤ (M / Real.sqrt (4 * Real.pi * D * t)) *
            (Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) :=
            mul_le_mul_of_nonneg_left hexp_split hA
        _ = (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
            * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by ring
    have hae : (fun x => gauss M D x t)
        ≤ᵐ[volume.restrict ((Ioo (-δ) δ)ᶜ)]
        (fun x => (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
          * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with x hx
      exact hpt x hx
    have hInt : IntegrableOn (fun x => gauss M D x t) ((Ioo (-δ) δ)ᶜ) :=
      (hKt t ht).integrableOn
    have hdom : Integrable
        (fun x => (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
          * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) (volume.restrict ((Ioo (-δ) δ)ᶜ)) := by
      have h := ((hbase.integrableOn : Integrable _ (volume.restrict ((Ioo (-δ) δ)ᶜ))).const_mul
        ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))))
      have heq : (fun x : ℝ => ((M / Real.sqrt (4 * Real.pi * D * t))
          * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))))
          = (fun x => (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
            * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
        funext x
        ring
      simpa [smul_eq_mul, heq] using h
    have hmono : (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t)
        ≤ ∫ x in (Ioo (-δ) δ)ᶜ, (M / Real.sqrt (4 * Real.pi * D * t))
          * Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      apply integral_mono_ae <;> assumption
    have hpull : (∫ x in (Ioo (-δ) δ)ᶜ, (M / Real.sqrt (4 * Real.pi * D * t))
        * Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))))
        = ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t))))
          * ∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      have heq : (fun x : ℝ => (M / Real.sqrt (4 * Real.pi * D * t))
          * Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))))
          = (fun x => ((M / Real.sqrt (4 * Real.pi * D * t))
            * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))) • Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
        funext x
        rw [smul_eq_mul]
      rw [heq, integral_smul, smul_eq_mul]
    have hsub : (∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t))))
        ≤ ∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      have hsp : (∫ x in Ioo (-δ) δ, Real.exp (-x ^ 2 / (2 * (4 * D * t))))
          + ∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t)))
          = ∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))) :=
        integral_add_compl measurableSet_Ioo hbase
      have hnn : (0 : ℝ) ≤ ∫ x in Ioo (-δ) δ, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
        have hae0 : ∀ᵐ x ∂(volume.restrict (Ioo (-δ) δ)),
            (0 : ℝ) ≤ Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
          filter_upwards with x
          exact (Real.exp_pos _).le
        exact MeasureTheory.integral_nonneg_of_ae hae0
      linarith
    have hgauss : (∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))))
        = Real.sqrt (2 * (4 * Real.pi * D * t)) := by
      simp_rw [hker2s]
      rw [integral_gaussian _]
      have hQ2 : Real.pi / (1 / (2 * (4 * D * t))) = 2 * (4 * Real.pi * D * t) := by
        field_simp
      rw [hQ2]
    have hEδ : Real.exp (-δ ^ 2 / (2 * (4 * D * t))) = Real.exp (-δ ^ 2 / (8 * D * t)) := by
      have h8 : (2 * (4 * D * t) : ℝ) = 8 * D * t := by ring
      rw [h8]
    have hsqrt8 : Real.sqrt (2 * (4 * Real.pi * D * t))
        = Real.sqrt 2 * Real.sqrt (4 * Real.pi * D * t) := by
      exact Real.sqrt_mul (by norm_num) _
    calc (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t)
        ≤ ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t))))
          * ∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
          rwa [← hpull]
      _ ≤ ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t))))
          * ∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
          refine mul_le_mul_of_nonneg_left hsub ?_
          exact mul_nonneg hA (Real.exp_pos _).le
      _ = M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
          rw [hgauss, hEδ, hsqrt8]
          field_simp
  have htail_lim : Tendsto
      (fun t => 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have hpos : (0 : ℝ) < δ ^ 2 / (8 * D) := by positivity
    have hneg : (-δ ^ 2 / (8 * D)) < 0 := by
      rw [show (-δ ^ 2 / (8 * D)) = -(δ ^ 2 / (8 * D)) by ring]
      exact neg_lt_zero.mpr hpos
    have hmul := hinv.const_mul_atTop_of_neg hneg
    have heq : (fun t : ℝ => (-δ ^ 2 / (8 * D)) * t⁻¹)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun t => -δ ^ 2 / (8 * D * t)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : (0 : ℝ) < t := Set.mem_Ioi.mp ht
      have ht' : t ≠ 0 := ne_of_gt htpos
      have h8D : (8 * D : ℝ) ≠ 0 := by positivity
      have h8Dt : (8 * D * t : ℝ) ≠ 0 := by positivity
      field_simp
    have hatBot : Tendsto (fun t : ℝ => -δ ^ 2 / (8 * D * t)) (𝓝[>] (0 : ℝ)) atBot :=
      hmul.congr' heq
    have hexp0 := Real.tendsto_exp_atBot.comp hatBot
    have hfull := hexp0.const_mul (2 * (|C| + 1) * M * Real.sqrt 2)
    have heq2 : (fun t : ℝ => 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)))
        = (fun t => (2 * (|C| + 1) * M * Real.sqrt 2)
          * ((Real.exp ∘ (fun t => -δ ^ 2 / (8 * D * t))) t)) := by
      funext t
      rfl
    rw [heq2]
    simpa using hfull
  have hev := (Metric.tendsto_nhds.mp htail_lim) (ε / 2) (half_pos hε)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff_ball.mp hev
  rw [eventually_nhdsWithin_iff]
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨η, hηpos, fun t htmem => ?_⟩
  intro htIoi
  have ht : (0 : ℝ) < t := Set.mem_Ioi.mp htIoi
  have hfar_lt : ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖ < ε / 2 := by
    have hfar_le : ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖
        ≤ 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
      have hpt2 : ∀ x ∈ (Ioo (-δ) δ)ᶜ,
          ‖gauss M D x t * (φ x - φ 0)‖ ≤ gauss M D x t * (2 * (|C| + 1)) := by
        intro x hx
        have hKnn : 0 ≤ gauss M D x t := gauss_nonneg M D x t hM hD ht
        have hφ2 : |φ x - φ 0| ≤ 2 * (|C| + 1) := by
          calc |φ x - φ 0| = |φ x + (-φ 0)| := by rw [sub_eq_add_neg]
            _ ≤ |φ x| + |-φ 0| := abs_add_le _ _
            _ = |φ x| + |φ 0| := by rw [abs_neg]
            _ ≤ 2 * (|C| + 1) := by linarith [hC' x, hC' 0]
        calc ‖gauss M D x t * (φ x - φ 0)‖
            = |gauss M D x t| * |φ x - φ 0| := by
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ = gauss M D x t * |φ x - φ 0| := by rw [abs_of_nonneg hKnn]
          _ ≤ gauss M D x t * (2 * (|C| + 1)) :=
              mul_le_mul_of_nonneg_left hφ2 hKnn
      have hae2 : (fun x => ‖gauss M D x t * (φ x - φ 0)‖)
          ≤ᵐ[volume.restrict ((Ioo (-δ) δ)ᶜ)]
          (fun x => gauss M D x t * (2 * (|C| + 1))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with x hx
        exact hpt2 x hx
      have hInt2 : Integrable (fun x => gauss M D x t * (φ x - φ 0))
          (volume.restrict ((Ioo (-δ) δ)ᶜ)) := (hfullint t ht).integrableOn
      have hnorm2 : IntegrableOn (fun x => ‖gauss M D x t * (φ x - φ 0)‖) ((Ioo (-δ) δ)ᶜ) :=
        ((hfullint t ht).integrableOn : Integrable _ (volume.restrict ((Ioo (-δ) δ)ᶜ))).norm
      have hconst2 : Integrable (fun x => gauss M D x t * (2 * (|C| + 1)))
          (volume.restrict ((Ioo (-δ) δ)ᶜ)) := by
        have h := (((hKt t ht).integrableOn :
          Integrable _ (volume.restrict ((Ioo (-δ) δ)ᶜ))).const_mul (2 * (|C| + 1)))
        have heq : (fun x : ℝ => (2 * (|C| + 1)) * gauss M D x t)
            = (fun x => gauss M D x t * (2 * (|C| + 1))) := by
          funext x
          ring
        simpa [smul_eq_mul, heq] using h
      have hpull2 : (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (2 * (|C| + 1)))
          = (2 * (|C| + 1)) * ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t := by
        have heq : (fun x : ℝ => gauss M D x t * (2 * (|C| + 1)))
            = (fun x => (2 * (|C| + 1)) • gauss M D x t) := by
          funext x
          rw [smul_eq_mul, mul_comm]
        rw [heq, integral_smul, smul_eq_mul]
      calc ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖
          ≤ ∫ x in (Ioo (-δ) δ)ᶜ, ‖gauss M D x t * (φ x - φ 0)‖ := by
            exact norm_integral_le_integral_norm _
        _ ≤ ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (2 * (|C| + 1)) := by
            apply integral_mono_ae <;> assumption
        _ = (2 * (|C| + 1)) * ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t := hpull2
        _ ≤ (2 * (|C| + 1)) * (M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t))) :=
            mul_le_mul_of_nonneg_left (htail t ht) (by positivity)
        _ = 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by ring
    have hbound_lt : dist (2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t))) 0
        < ε / 2 := hη t htmem htIoi
    have hbound_nn : (0 : ℝ)
        ≤ 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
      positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbound_nn] at hbound_lt
    linarith [hfar_le, hbound_lt]
  have hnear_le := hnear t ht
  have hdecomp' : (∫ x, gauss M D x t * φ x) - M * φ 0
      = (∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))
        + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0) := by
    rw [hdecomp t ht, hsplit t ht]
  rw [Real.dist_eq, hdecomp']
  calc |(∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))
      + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)|
      ≤ |(∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))|
        + |∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)| := abs_add_le _ _
    _ = ‖∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0)‖
        + ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hnear_le hfar_lt
    _ = ε := add_halves ε

/-!

## C. The complementary error function profile

-/

/-!

### C.1. The complementary error function

-/

/-- The complementary error function `erfc x = 1 - (2/√π) ∫₀ˣ exp(-s²) ds`, defined here from
the Gaussian integral because the pinned Mathlib has no error function. It is defined for every
real `x`. -/
noncomputable def erfc (x : ℝ) : ℝ :=
  1 - (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- The derivative `erfc' x = -(2/√π) exp(-x²)` of `erfc` (see `hasDerivAt_erfc`). -/
noncomputable def erfcDeriv (x : ℝ) : ℝ :=
  -(2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2)

/-- The second derivative `erfc'' x = (4x/√π) exp(-x²)` of `erfc`
(see `hasDerivAt_erfcDeriv`). -/
noncomputable def erfcDeriv2 (x : ℝ) : ℝ :=
  (4 * x / Real.sqrt Real.pi) * Real.exp (-x ^ 2)

/-- `erfc 0 = 1`. -/
lemma erfc_zero : erfc 0 = 1 := by
  simp only [erfc, intervalIntegral.integral_same, mul_zero, sub_zero]

/-- `erfc` has the derivative `erfcDeriv x` at every `x` (fundamental theorem of
calculus). -/
lemma hasDerivAt_erfc (x : ℝ) : HasDerivAt erfc (erfcDeriv x) x := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-t ^ 2)) :=
    Real.continuous_exp.comp ((continuous_id.pow 2).neg)
  have hFTC := hcont.integral_hasStrictDerivAt 0 x
  have h := (hFTC.hasDerivAt.const_mul (2 / Real.sqrt Real.pi)).const_sub 1
  have hval : (-((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2))) = erfcDeriv x := by
    simp only [erfcDeriv]
    ring
  rwa [hval] at h

/-- `erfcDeriv` has the derivative `erfcDeriv2 x` at every `x`. -/
lemma hasDerivAt_erfcDeriv (x : ℝ) : HasDerivAt erfcDeriv (erfcDeriv2 x) x := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hu : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * x)) x := hpow.neg
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2))
      (Real.exp (-x ^ 2) * (-(2 * x))) x := by
    simpa using hu.exp
  have hraw : HasDerivAt (fun x : ℝ => -(2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2))
      ((-(2 / Real.sqrt Real.pi)) * (Real.exp (-x ^ 2) * (-(2 * x)))) x := by
    simpa using hexp.const_mul (-(2 / Real.sqrt Real.pi))
  have hval : ((-(2 / Real.sqrt Real.pi)) * (Real.exp (-x ^ 2) * (-(2 * x))))
      = erfcDeriv2 x := by
    simp only [erfcDeriv2]
    ring
  rwa [hval] at hraw

/-- `erfc` satisfies `erfc'' + 2x erfc' = 0`, written with the explicit derivatives
`erfcDeriv2` and `erfcDeriv`. -/
lemma erfc_ode (x : ℝ) : erfcDeriv2 x + 2 * x * erfcDeriv x = 0 := by
  simp only [erfcDeriv, erfcDeriv2]
  ring

/-- `erfc` is strictly decreasing on the whole line. -/
lemma erfc_strictAnti : StrictAntiOn erfc Set.univ := by
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), deriv erfc x < 0 := by
    intro x _
    have h := (hasDerivAt_erfc x).deriv
    rw [h]
    simp only [erfcDeriv]
    have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have he : (0 : ℝ) < Real.exp (-x ^ 2) := Real.exp_pos _
    have h2 : (0 : ℝ) < 2 / Real.sqrt Real.pi := div_pos (by norm_num) hpi
    have hAlt : (-(2 / Real.sqrt Real.pi)) < 0 := by linarith
    exact mul_neg_of_neg_of_pos hAlt he
  have hderiv' : ∀ x ∈ interior (Set.univ : Set ℝ), deriv erfc x < 0 := by
    intro x hx
    rw [interior_univ] at hx
    exact hderiv x hx
  have hconv : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have hcont : ContinuousOn erfc (Set.univ : Set ℝ) :=
    fun x _ => (hasDerivAt_erfc x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ erfc (Set.univ : Set ℝ) :=
    fun x _ => (hasDerivAt_erfc x).differentiableAt.differentiableWithinAt
  apply strictAntiOn_of_deriv_neg <;> assumption

/-- The half-line Gaussian integral `∫₀^∞ exp(-t²) dt = √π / 2`, from Mathlib's
`integral_gaussian_Ioi`. -/
private lemma integral_exp_neg_sq_Ioi :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 := by
  simpa using integral_gaussian_Ioi 1

/-- `erfc x → 0` as `x → ∞`. -/
lemma erfc_tendsto_atTop : Tendsto erfc atTop (𝓝 0) := by
  have hker : ∀ t : ℝ, (-t ^ 2) = (-(1 : ℝ) * t ^ 2) := fun t => by ring
  have hint : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simp_rw [hker]
    apply integrable_exp_neg_mul_sq
    norm_num
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi 0) := hint.integrableOn
  have hlim : Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))) := by
    apply intervalIntegral_tendsto_integral_Ioi
    · assumption
    · exact tendsto_id
  have hmul := hlim.const_mul (2 / Real.sqrt Real.pi)
  have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub := h1.sub hmul
  have hcongr : Tendsto erfc atTop (𝓝 (1 - (2 / Real.sqrt Real.pi)
      * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))) := by
    have heq : erfc =ᶠ[atTop] ((fun _ : ℝ => 1) - fun x => (2 / Real.sqrt Real.pi)
        * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) := by
      filter_upwards with x
      rfl
    exact hsub.congr' heq
  rw [integral_exp_neg_sq_Ioi] at hcongr
  have hval : (1 : ℝ) - (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 0 := by
    have hsq : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
    ring
  rwa [hval] at hcongr

/-- For `u ≥ 0`, `erfc u = (2/√π) ∫ᵤ^∞ exp(-v²) dv`. -/
lemma erfc_tail (u : ℝ) (hu : 0 ≤ u) :
    erfc u = (2 / Real.sqrt Real.pi) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2) := by
  have hker : ∀ t : ℝ, (-t ^ 2) = (-(1 : ℝ) * t ^ 2) := fun t => by ring
  have hint : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simp_rw [hker]
    apply integrable_exp_neg_mul_sq
    norm_num
  have hFIoc : (∫ t in (0 : ℝ)..u, Real.exp (-t ^ 2))
      = ∫ t in Set.Ioc 0 u, Real.exp (-t ^ 2) := intervalIntegral.integral_of_le hu
  have hunion : Set.Ioc (0 : ℝ) u ∪ Set.Ioi u = Set.Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx0, -⟩ | hxu)
      · exact hx0
      · exact lt_of_le_of_lt hu hxu
    · intro hx0
      rcases lt_or_ge x u with hxu | hxu
      · exact Or.inl ⟨hx0, le_of_lt hxu⟩
      · rcases eq_or_lt_of_le hxu with rfl | hux
        · exact Or.inl ⟨hx0, le_rfl⟩
        · exact Or.inr hux
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))
      = (∫ t in Set.Ioc 0 u, Real.exp (-t ^ 2)) + ∫ t in Set.Ioi u, Real.exp (-t ^ 2) := by
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) u) (Set.Ioi u) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h1 : x ≤ u := (Set.mem_Ioc.mp hx1).2
      have h2 : u < x := Set.mem_Ioi.mp hx2
      linarith
    have hm1 : MeasurableSet (Set.Ioc (0 : ℝ) u) := measurableSet_Ioc
    have hm2 : MeasurableSet (Set.Ioi u) := measurableSet_Ioi
    have hU : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioc 0 u ∪ Set.Ioi u) :=
      hint.integrableOn
    have hIoc : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioc 0 u) := hint.integrableOn
    have hIoiu : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi u) := hint.integrableOn
    rw [← hunion]
    apply setIntegral_union <;> assumption
  have hC : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    have hsq : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
  have hH : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 :=
    integral_exp_neg_sq_Ioi
  have htail : (∫ t in Set.Ioi u, Real.exp (-t ^ 2))
      = Real.sqrt Real.pi / 2 - ∫ t in Set.Ioc 0 u, Real.exp (-t ^ 2) := by
    linarith [hsplit, hH]
  simp only [erfc]
  rw [hFIoc, ← hC, htail]
  ring

/-- `erfc` is nonnegative on `[0, ∞)`. -/
lemma erfc_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ erfc u := by
  rw [erfc_tail u hu]
  have hC : (0 : ℝ) ≤ 2 / Real.sqrt Real.pi :=
    div_nonneg (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).le
  have hnn : (0 : ℝ) ≤ ∫ v in Set.Ioi u, Real.exp (-v ^ 2) := by
    have hae : ∀ᵐ v ∂(volume.restrict (Set.Ioi u)), (0 : ℝ) ≤ Real.exp (-v ^ 2) := by
      filter_upwards with v
      exact (Real.exp_pos _).le
    exact integral_nonneg_of_ae hae
  exact mul_nonneg hC hnn

/-- A Gaussian upper bound on `[0, ∞)`: `erfc u ≤ 2√2 exp(-u²/2)` for `u ≥ 0`. -/
lemma erfc_le_gauss (u : ℝ) (hu : 0 ≤ u) :
    erfc u ≤ 2 * Real.sqrt 2 * Real.exp (-u ^ 2 / 2) := by
  have hker : ∀ v : ℝ, (-v ^ 2 / 2) = (-(1 / 2 : ℝ) * v ^ 2) := fun v => by ring
  have hgauss : (∫ v : ℝ, Real.exp (-v ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
    simp_rw [hker]
    have h := integral_gaussian (1 / 2 : ℝ)
    have hQ : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by
      field_simp
    rw [hQ] at h
    exact h
  have hint : Integrable (fun v : ℝ => Real.exp (-v ^ 2 / 2)) := by
    simp_rw [hker]
    apply integrable_exp_neg_mul_sq
    norm_num
  have hpt : ∀ v ∈ Set.Ioi u, Real.exp (-v ^ 2)
      ≤ Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2) := by
    intro v hv
    have hvu : u ≤ v := le_of_lt (Set.mem_Ioi.mp hv)
    have h2 : u ^ 2 ≤ v ^ 2 := by gcongr
    have harg : -v ^ 2 ≤ (-u ^ 2 / 2) + (-v ^ 2 / 2) := by linarith [h2]
    calc Real.exp (-v ^ 2) ≤ Real.exp ((-u ^ 2 / 2) + (-v ^ 2 / 2)) :=
          Real.exp_le_exp.mpr harg
      _ = Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2) := Real.exp_add _ _
  have hae : (fun v => Real.exp (-v ^ 2))
      ≤ᵐ[volume.restrict (Set.Ioi u)]
      (fun v => Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hpt v hv
  have hInt : IntegrableOn (fun v => Real.exp (-v ^ 2)) (Set.Ioi u) := by
    have hker1 : ∀ v : ℝ, (-v ^ 2) = (-(1 : ℝ) * v ^ 2) := fun v => by ring
    have hfull : Integrable (fun v : ℝ => Real.exp (-v ^ 2)) := by
      simp_rw [hker1]
      apply integrable_exp_neg_mul_sq
      norm_num
    exact hfull.integrableOn
  have hdom : Integrable
      (fun v => Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2)) (volume.restrict (Set.Ioi u)) := by
    simpa [smul_eq_mul] using
      ((hint.integrableOn : Integrable _ (volume.restrict (Set.Ioi u))).const_mul _)
  have hmono : (∫ v in Set.Ioi u, Real.exp (-v ^ 2))
      ≤ ∫ v in Set.Ioi u, Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2) := by
    apply integral_mono_ae <;> assumption
  have hpull : (∫ v in Set.Ioi u, Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2))
      = Real.exp (-u ^ 2 / 2) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2) := by
    have heq : (fun v : ℝ => Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2))
        = (fun v => Real.exp (-u ^ 2 / 2) • Real.exp (-v ^ 2 / 2)) := by
      funext v
      rw [smul_eq_mul]
    rw [heq, integral_smul, smul_eq_mul]
  have hsub : (∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2))
      ≤ ∫ v, Real.exp (-v ^ 2 / 2) := by
    have hsp : (∫ v in (Set.Ioi u)ᶜ, Real.exp (-v ^ 2 / 2))
        + ∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2) = ∫ v, Real.exp (-v ^ 2 / 2) := by
      have h := integral_add_compl (s := Set.Ioi u) measurableSet_Ioi hint
      linarith
    have hnn : (0 : ℝ) ≤ ∫ v in (Set.Ioi u)ᶜ, Real.exp (-v ^ 2 / 2) := by
      have hae0 : ∀ᵐ v ∂(volume.restrict ((Set.Ioi u)ᶜ)),
          (0 : ℝ) ≤ Real.exp (-v ^ 2 / 2) := by
        filter_upwards with v
        exact (Real.exp_pos _).le
      exact integral_nonneg_of_ae hae0
    linarith
  rw [erfc_tail u hu]
  calc (2 / Real.sqrt Real.pi) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2)
      ≤ (2 / Real.sqrt Real.pi)
        * (Real.exp (-u ^ 2 / 2) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (div_nonneg (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).le)
        rw [← hpull]
        exact hmono
    _ ≤ (2 / Real.sqrt Real.pi) * (Real.exp (-u ^ 2 / 2) * ∫ v, Real.exp (-v ^ 2 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (div_nonneg (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).le)
        exact mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le
    _ = 2 * Real.sqrt 2 * Real.exp (-u ^ 2 / 2) := by
        rw [hgauss]
        have h2nn : (0 : ℝ) ≤ 2 := by norm_num
        have hpin : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
        have hsqrt2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
          exact Real.sqrt_mul h2nn _
        rw [hsqrt2]
        have hsq : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
        field_simp

/-!

### C.2. The profile and the diffusion equation

-/

/-- The constant-surface-concentration profile on the half-line `x ≥ 0`:
`erfcProfile cs D x t = cs · erfc(x / √(4Dt))`, the concentration at depth `x` and time `t` when
the surface `x = 0` is held at `cs` and the medium is initially empty. It is meant for `D > 0`,
`t > 0` and `x ≥ 0`. For `D > 0` and `t ≤ 0` the square root is `0`, `x / 0 = 0` and the value is
`cs` at every `x` (Lean's division convention), not the initial concentration `0`; the initial
condition is the limit `erfcProfile_initial`. -/
noncomputable def erfcProfile (cs D x t : ℝ) : ℝ :=
  cs * erfc (x / Real.sqrt (4 * D * t))

/-- The spatial derivative of the profile for `D > 0` and `t > 0`:
`∂ₓ erfcProfile = (cs / √(4Dt)) · erfc'(x / √(4Dt))`. -/
lemma erfcProfile_xderiv_value (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => erfcProfile cs D x t)
      ((cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))) x := by
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hu := (hasDerivAt_id' x).div_const (Real.sqrt (4 * D * t))
  have hcomp := (hasDerivAt_erfc (x / Real.sqrt (4 * D * t))).comp x hu
  have hchain := hcomp.const_mul cs
  change HasDerivAt (fun x => cs * erfc (x / Real.sqrt (4 * D * t)))
    ((cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))) x
  have hderiv : (cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))
      = cs * (erfcDeriv (x / Real.sqrt (4 * D * t)) * (1 / Real.sqrt (4 * D * t))) := by
    ring
  rw [hderiv]
  exact hchain

/-- The second spatial derivative of the profile for `D > 0` and `t > 0`:
`∂ₓₓ erfcProfile = cs · erfc''(x / √(4Dt)) / (√(4Dt))²`. -/
lemma erfcProfile_xxderiv_value (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => deriv (fun x' => erfcProfile cs D x' t) x)
      (cs * erfcDeriv2 (x / Real.sqrt (4 * D * t)) / (Real.sqrt (4 * D * t)) ^ 2) x := by
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs2 : (Real.sqrt (4 * D * t)) ^ 2 ≠ 0 := pow_ne_zero 2 hs'
  have hfun : (fun x => deriv (fun x' => erfcProfile cs D x' t) x)
      = (fun x => (cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))) := by
    funext x'
    exact (erfcProfile_xderiv_value cs D x' t hD ht).deriv
  rw [hfun]
  have hu := (hasDerivAt_id' x).div_const (Real.sqrt (4 * D * t))
  have hcomp := (hasDerivAt_erfcDeriv (x / Real.sqrt (4 * D * t))).comp x hu
  have hchain := hcomp.const_mul (cs / Real.sqrt (4 * D * t))
  have hderiv : cs * erfcDeriv2 (x / Real.sqrt (4 * D * t)) / (Real.sqrt (4 * D * t)) ^ 2
      = (cs / Real.sqrt (4 * D * t)) *
        (erfcDeriv2 (x / Real.sqrt (4 * D * t)) * (1 / Real.sqrt (4 * D * t))) := by
    field_simp [hs', hs2]
  rw [hderiv]
  exact hchain

/-- The time derivative of the profile for `D > 0` and `t > 0`, by the chain rule through
`x / √(4Dt)`. -/
lemma erfcProfile_tderiv_value (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun t => erfcProfile cs D x t)
      (cs * (erfcDeriv (x / Real.sqrt (4 * D * t))
        * ((0 * Real.sqrt (4 * D * t) - x * ((4 * D) / (2 * Real.sqrt (4 * D * t))))
          / (Real.sqrt (4 * D * t)) ^ 2))) t := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have h4Dt : (0 : ℝ) < 4 * D * t := by positivity
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h4Dt)
  have hs2 : (Real.sqrt (4 * D * t)) ^ 2 ≠ 0 := pow_ne_zero 2 hs'
  have h2s : (2 * Real.sqrt (4 * D * t) : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hs'
  have hlin : HasDerivAt (fun t : ℝ => 4 * D * t) (4 * D) t := by
    simpa using (hasDerivAt_id' t).const_mul (4 * D)
  have hsqrt := hlin.sqrt (show (fun t : ℝ => 4 * D * t) t ≠ 0 from ne_of_gt h4Dt)
  have hxi := (hasDerivAt_const t x).div hsqrt
    (show (fun t : ℝ => Real.sqrt (4 * D * t)) t ≠ 0 from hs')
  have hcomp := (hasDerivAt_erfc (x / Real.sqrt (4 * D * t))).comp t hxi
  have hchain := hcomp.const_mul cs
  exact hchain

/-- **The error-function profile solves the diffusion equation.** For `D > 0`, `t > 0` and
every real `cs` and `x`, `∂ₜ erfcProfile = D ∂ₓₓ erfcProfile` at `(x, t)`. -/
theorem erfcProfile_pde (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun t => erfcProfile cs D x t) t
      = D * deriv (fun x => deriv (fun x' => erfcProfile cs D x' t) x) x := by
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs2 : (Real.sqrt (4 * D * t)) ^ 2 ≠ 0 := pow_ne_zero 2 hs'
  have h2s : (2 * Real.sqrt (4 * D * t) : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hs'
  have hD' : D ≠ 0 := ne_of_gt hD
  rw [(erfcProfile_tderiv_value cs D x t hD ht).deriv,
    (erfcProfile_xxderiv_value cs D x t hD ht).deriv]
  have hE2 : erfcDeriv2 (x / Real.sqrt (4 * D * t))
      = -2 * (x / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t)) := by
    have hode := erfc_ode (x / Real.sqrt (4 * D * t))
    linarith
  rw [hE2]
  field_simp
  ring

/-!

### C.3. Surface, far-field and initial values

-/

/-- The surface is held at the concentration `cs`: `erfcProfile cs D 0 t = cs`. -/
lemma erfcProfile_surface (cs D t : ℝ) (_ht : 0 < t) (_hD : 0 < D) :
    erfcProfile cs D 0 t = cs := by
  simp only [erfcProfile]
  have h0 : (0 : ℝ) / Real.sqrt (4 * D * t) = 0 := zero_div _
  rw [h0, erfc_zero, mul_one]

/-- For `D > 0` and `t > 0`, the profile vanishes far from the surface:
`erfcProfile cs D x t → 0` as `x → ∞`. -/
lemma erfcProfile_farfield (cs D t : ℝ) (ht : 0 < t) (hD : 0 < D) :
    Tendsto (fun x => erfcProfile cs D x t) atTop (𝓝 0) := by
  have hs : (0 : ℝ) < Real.sqrt (4 * D * t) := Real.sqrt_pos.mpr (by positivity)
  have hsinv : (0 : ℝ) < (Real.sqrt (4 * D * t))⁻¹ := inv_pos.mpr hs
  have harg : Tendsto (fun x : ℝ => x / Real.sqrt (4 * D * t)) atTop atTop := by
    have hmul := tendsto_id.const_mul_atTop hsinv
    simpa [div_eq_mul_inv, mul_comm] using hmul
  have herfc := erfc_tendsto_atTop.comp harg
  have hcs := herfc.const_mul cs
  have heq : (fun x : ℝ => erfcProfile cs D x t)
      = (fun x => cs * ((erfc ∘ (fun x => x / Real.sqrt (4 * D * t))) x)) := by
    funext x
    rfl
  rw [heq]
  simpa using hcs

/-- The medium is initially empty: for `x > 0` and `D > 0`, `erfcProfile cs D x t → 0` as
`t → 0⁺`. The value at `t = 0` itself is the junk value `cs` (see `erfcProfile`). -/
lemma erfcProfile_initial (cs D x : ℝ) (hx : 0 < x) (hD : 0 < D) :
    Tendsto (fun t => erfcProfile cs D x t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have harg : Tendsto (fun t : ℝ => x / Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ)) atTop := by
    have hsqrt0 : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ)) := by
      have hcont : ContinuousAt (fun t : ℝ => Real.sqrt (4 * D * t)) 0 :=
        (Real.continuous_sqrt.comp (continuous_id.const_mul (4 * D))).continuousAt
      have hval : (fun t : ℝ => Real.sqrt (4 * D * t)) 0 = 0 := by simp
      have htend : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝 0)
          (𝓝 ((fun t : ℝ => Real.sqrt (4 * D * t)) 0)) := hcont
      have hlim : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ))
            (𝓝 ((fun t : ℝ => Real.sqrt (4 * D * t)) 0)) :=
          htend.mono_left nhdsWithin_le_nhds
        rwa [hval] at h
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hlim, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : (0 : ℝ) < t := Set.mem_Ioi.mp ht
      have hpos : (0 : ℝ) < 4 * D * t := by positivity
      exact Real.sqrt_pos.mpr hpos
    have hinv : Tendsto (fun t : ℝ => (Real.sqrt (4 * D * t))⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp hsqrt0
    have hmul := hinv.const_mul_atTop hx
    have heq : (fun t : ℝ => x * (Real.sqrt (4 * D * t))⁻¹)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun t => x / Real.sqrt (4 * D * t)) := by
      filter_upwards with t
      exact (div_eq_mul_inv _ _).symm
    exact hmul.congr' heq
  have herfc := erfc_tendsto_atTop.comp harg
  have hcs := herfc.const_mul cs
  have heq : (fun t : ℝ => erfcProfile cs D x t)
      = (fun t => cs * ((erfc ∘ (fun t => x / Real.sqrt (4 * D * t))) t)) := by
    funext t
    rfl
  rw [heq]
  simpa using hcs

/-!

### C.4. Mass uptake through the surface

-/

/-- For `cs > 0`, `D > 0` and `t > 0`, the profile is integrable on `(0, ∞)`: it is dominated
by `cs · 2√2 · exp(-x² / (2 (√(4Dt))²))`. -/
lemma erfcProfile_integrableOn (cs D t : ℝ) (hcs : 0 < cs) (hD : 0 < D) (ht : 0 < t) :
    IntegrableOn (fun x => erfcProfile cs D x t) (Set.Ioi 0) := by
  have ha : (0 : ℝ) < Real.sqrt (4 * D * t) := Real.sqrt_pos.mpr (by positivity)
  have ha' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt ha
  have h2a2 : (2 * (Real.sqrt (4 * D * t)) ^ 2 : ℝ) ≠ 0 := by positivity
  have hb : (0 : ℝ) < 1 / (2 * (Real.sqrt (4 * D * t)) ^ 2) := by positivity
  have hker : ∀ x : ℝ, (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))
      = (-(1 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) * x ^ 2) := by
    intro x
    field_simp
  have hbase :
      Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))) := by
    simp_rw [hker]
    exact integrable_exp_neg_mul_sq hb
  have hdom : Integrable (fun x : ℝ => cs * 2 * Real.sqrt 2
      * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))) := by
    simpa [smul_eq_mul] using hbase.const_mul (cs * 2 * Real.sqrt 2)
  have hcont : Continuous (fun x : ℝ => erfcProfile cs D x t) := by
    have herfc : Continuous erfc := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (hasDerivAt_erfc x).continuousAt
    exact (herfc.comp (continuous_id.div_const (Real.sqrt (4 * D * t)))).const_mul cs
  have hmeas : AEStronglyMeasurable (fun x => erfcProfile cs D x t)
      (volume.restrict (Set.Ioi 0)) :=
    hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖erfcProfile cs D x t‖ ≤ cs * 2 * Real.sqrt 2
        * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
    have hu : (0 : ℝ) ≤ x / Real.sqrt (4 * D * t) := div_nonneg hx0 ha.le
    have hle := erfc_le_gauss (x / Real.sqrt (4 * D * t)) hu
    have hexp_eq : (-(x / Real.sqrt (4 * D * t)) ^ 2 / 2)
        = (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) := by
      field_simp
    rw [hexp_eq] at hle
    have hnn : 0 ≤ erfcProfile cs D x t :=
      mul_nonneg hcs.le (erfc_nonneg _ hu)
    calc ‖erfcProfile cs D x t‖ = |erfcProfile cs D x t| := Real.norm_eq_abs _
      _ = erfcProfile cs D x t := abs_of_nonneg hnn
      _ = cs * erfc (x / Real.sqrt (4 * D * t)) := rfl
      _ ≤ cs * (2 * Real.sqrt 2 * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))) :=
          mul_le_mul_of_nonneg_left hle hcs.le
      _ = cs * 2 * Real.sqrt 2 * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) := by ring
  have hdomR : Integrable (fun x : ℝ => cs * 2 * Real.sqrt 2
      * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)))
      (volume.restrict (Set.Ioi 0)) := hdom.integrableOn
  exact Integrable.mono' hdomR hmeas hbound

/-- For `x > 0`, `cs > 0` and `D > 0`, the concentration at depth `x` strictly increases in
time: `erfcProfile cs D x t₁ < erfcProfile cs D x t₂` for `0 < t₁ < t₂`. -/
lemma profile_pointwise_lt (cs D x t₁ t₂ : ℝ) (hx : 0 < x) (hcs : 0 < cs) (hD : 0 < D)
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (h12 : t₁ < t₂) :
    erfcProfile cs D x t₁ < erfcProfile cs D x t₂ := by
  have ha : Real.sqrt (4 * D * t₁) < Real.sqrt (4 * D * t₂) := by
    refine Real.sqrt_lt_sqrt (by positivity) ?_
    have h4D : (0 : ℝ) < 4 * D := by positivity
    exact mul_lt_mul_of_pos_left h12 h4D
  have ha1 : (0 : ℝ) < Real.sqrt (4 * D * t₁) := Real.sqrt_pos.mpr (by positivity)
  have ha2 : (0 : ℝ) < Real.sqrt (4 * D * t₂) := Real.sqrt_pos.mpr (by positivity)
  have harg : x / Real.sqrt (4 * D * t₂) < x / Real.sqrt (4 * D * t₁) := by
    gcongr
  have herfc := erfc_strictAnti (Set.mem_univ _) (Set.mem_univ _) harg
  simp only [erfcProfile]
  exact mul_lt_mul_of_pos_left herfc hcs

/-- **Mass uptake.** For `cs > 0` and `D > 0`, the amount `∫₀^∞ erfcProfile cs D x t dx` on the
half-line is strictly increasing in `t > 0`: the surface held at `cs` supplies mass. Its closed
form `2 cs √(Dt/π)` is not proved here. -/
lemma erfcProfile_mass_strictMono (cs D : ℝ) (hcs : 0 < cs) (hD : 0 < D) :
    StrictMonoOn (fun t => ∫ x in Set.Ioi (0 : ℝ), erfcProfile cs D x t) (Set.Ioi (0 : ℝ)) := by
  intro t₁ ht₁ t₂ ht₂ h12
  have ht₁' : (0 : ℝ) < t₁ := Set.mem_Ioi.mp ht₁
  have ht₂' : (0 : ℝ) < t₂ := Set.mem_Ioi.mp ht₂
  have hint1 := erfcProfile_integrableOn cs D t₁ hcs hD ht₁'
  have hint2 := erfcProfile_integrableOn cs D t₂ hcs hD ht₂'
  have hsub : (∫ x in Set.Ioi (0 : ℝ), erfcProfile cs D x t₂)
      - ∫ x in Set.Ioi (0 : ℝ), erfcProfile cs D x t₁
      = ∫ x in Set.Ioi (0 : ℝ), (erfcProfile cs D x t₂ - erfcProfile cs D x t₁) := by
    have g1 : Integrable (fun x => erfcProfile cs D x t₁) (volume.restrict (Set.Ioi 0)) := hint1
    have g2 : Integrable (fun x => erfcProfile cs D x t₂) (volume.restrict (Set.Ioi 0)) := hint2
    exact (integral_sub g2 g1).symm
  suffices hpos : (0 : ℝ)
      < ∫ x in Set.Ioi (0 : ℝ), (erfcProfile cs D x t₂ - erfcProfile cs D x t₁) by
    linarith [hsub]
  have hnn : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (0 : ℝ) ≤ erfcProfile cs D x t₂ - erfcProfile cs D x t₁ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (0 : ℝ) < x := Set.mem_Ioi.mp hx
    have hlt := profile_pointwise_lt cs D x t₁ t₂ hx' hcs hD ht₁' ht₂' h12
    linarith
  have hint_sub : Integrable (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have g1 : Integrable (fun x => erfcProfile cs D x t₁) (volume.restrict (Set.Ioi 0)) := hint1
    have g2 : Integrable (fun x => erfcProfile cs D x t₂) (volume.restrict (Set.Ioi 0)) := hint2
    exact g2.sub g1
  have hiff : (0 : ℝ) < ∫ x in Set.Ioi (0 : ℝ), (erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
      ↔ 0 < (volume.restrict (Set.Ioi (0 : ℝ)))
        (Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)) :=
    integral_pos_iff_support_of_nonneg_ae hnn hint_sub
  have hsupp_pos : (0 : ENNReal) < (volume.restrict (Set.Ioi (0 : ℝ)))
      (Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)) := by
    have hsub2 : Set.Ioo (1 / 2 : ℝ) 1
        ⊆ Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
          ∩ Set.Ioi (0 : ℝ) := by
      intro x hx
      have hx1 : (1 / 2 : ℝ) < x := (Set.mem_Ioo.mp hx).1
      have hx' : (0 : ℝ) < x := by linarith
      have hlt := profile_pointwise_lt cs D x t₁ t₂ hx' hcs hD ht₁' ht₂' h12
      constructor
      · rw [Function.mem_support]
        exact ne_of_gt (by linarith [hlt] : (0 : ℝ) < erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
      · exact Set.mem_Ioi.mpr hx'
    have hmeas : volume (Set.Ioo (1 / 2 : ℝ) 1) = ENNReal.ofReal (1 - 1 / 2) := Real.volume_Ioo
    have h1 : volume (Set.Ioo (1 / 2 : ℝ) 1)
        ≤ (volume.restrict (Set.Ioi (0 : ℝ)))
          (Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)) := by
      rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioi]
      exact measure_mono hsub2
    have h2 : (0 : ENNReal) < volume (Set.Ioo (1 / 2 : ℝ) 1) := by
      rw [hmeas]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    exact lt_of_lt_of_le h2 h1
  exact hiff.mpr hsupp_pos

/-!

## D. Uniqueness for the Dirichlet problem

The energy method on the closed rectangle `[a, b] × [0, T]`. The difference `w` of two solutions
and its derivatives `wx`, `wxx`, `wt` are given explicitly. Continuity is assumed on the
rectangle (for `w`) or on `[a, b] × (0, T)` (for the derivatives), and the derivative relations,
the diffusion equation and the boundary values only at interior points and times. Nothing is
assumed outside the rectangle.

-/

/-- Integration by parts with zero boundary values: if `f` and `f'` are continuous on `[a, b]`,
`f'` and `f''` are the derivatives of `f` and `f'` on `(a, b)`, `f''` is continuous on `[a, b]`,
and `f a = f b = 0`, then `∫ₐᵇ f f'' = -∫ₐᵇ (f')²`. -/
private lemma integral_mul_deriv_deriv_eq_neg {a b : ℝ} (hab : a ≤ b) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hf'' : ContinuousOn f'' (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hd' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (ha : f a = 0) (hb : f b = 0) :
    ∫ x in a..b, f x * f'' x = -∫ x in a..b, f' x ^ 2 := by
  rw [← uIcc_of_le hab] at hf hf' hf''
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hf hf'
    (by simpa [min_eq_left hab, max_eq_right hab] using hd)
    (by simpa [min_eq_left hab, max_eq_right hab] using hd')
    hf'.intervalIntegrable hf''.intervalIntegrable
  have h1 : IntervalIntegrable (fun x => f' x * f' x) volume a b :=
    (hf'.mul hf').intervalIntegrable
  have h2 : IntervalIntegrable (fun x => f x * f'' x) volume a b :=
    (hf.mul hf'').intervalIntegrable
  rw [ha, hb, zero_mul, zero_mul, sub_self, intervalIntegral.integral_add h1 h2] at hibp
  have hsq : ∫ x in a..b, f' x ^ 2 = ∫ x in a..b, f' x * f' x := by
    simp only [sq]
  linarith

/-- The energy `t ↦ ∫ₐᵇ w(x, t)² dx` is continuous on `[0, T]` when `a ≤ b` and `w` is
continuous on the closed rectangle `[a, b] × [0, T]`. -/
lemma continuousOn_energy {a b T : ℝ} (hab : a ≤ b) {w : ℝ → ℝ → ℝ}
    (hw : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc a b ×ˢ Icc 0 T)) :
    ContinuousOn (fun t => ∫ x in a..b, w x t ^ 2) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (hw.pow 2)
  simp only [intervalIntegral.integral_of_le hab]
  refine continuousOn_of_dominated (bound := fun _ => C) (fun t ht => ?_) (fun t ht => ?_)
    (integrable_const C) ?_
  · exact ((hw.comp (continuous_id.prodMk continuous_const).continuousOn
      fun x hx => ⟨Ioc_subset_Icc_self hx, ht⟩).pow 2).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC (x, t) ⟨Ioc_subset_Icc_self hx, ht⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (hw.comp (continuous_const.prodMk continuous_id).continuousOn
      fun t ht => ⟨Ioc_subset_Icc_self hx, ht⟩).pow 2

/-- **Energy identity at an interior time.** Let `w` and the functions `wx`, `wxx`, `wt` be
continuous on `[a, b] × (0, T)`; let `wx`, `wxx`, `wt` be the derivatives `∂ₓw`, `∂ₓₓw`, `∂ₜw`
at the points of `(a, b) × (0, T)`, where `∂ₜw = D ∂ₓₓw`; and let `w` vanish at `x = a` and
`x = b` for `0 < t < T`. Then at every `t₀ ∈ (0, T)` the energy `E(t) = ∫ₐᵇ w(x, t)² dx` has the
derivative `-2D ∫ₐᵇ wx(x, t₀)² dx`. -/
lemma energy_identity_deriv {a b T D : ℝ} (hab : a < b) {w wx wxx wt : ℝ → ℝ → ℝ}
    (hw_cont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc a b ×ˢ Ioo 0 T))
    (hwx_cont : ContinuousOn (fun p : ℝ × ℝ => wx p.1 p.2) (Icc a b ×ˢ Ioo 0 T))
    (hwxx_cont : ContinuousOn (fun p : ℝ × ℝ => wxx p.1 p.2) (Icc a b ×ˢ Ioo 0 T))
    (hwt_cont : ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2) (Icc a b ×ˢ Ioo 0 T))
    (ht : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, HasDerivAt (fun τ => w x τ) (wt x t) t)
    (hx : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => w u t) (wx x t) x)
    (hxx : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => wx u t) (wxx x t) x)
    (hpde : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, wt x t = D * wxx x t)
    (hbc : ∀ t ∈ Ioo 0 T, w a t = 0 ∧ w b t = 0) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    HasDerivAt (fun t => ∫ x in a..b, w x t ^ 2) (-2 * D * ∫ x in a..b, wx x t₀ ^ 2) t₀ := by
  -- slices in space of a function continuous on the strip are continuous
  have slice : ∀ {g : ℝ → ℝ → ℝ},
      ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc a b ×ˢ Ioo 0 T) →
      ∀ t ∈ Ioo 0 T, ContinuousOn (fun x => g x t) (Icc a b) := fun hg t ht =>
    hg.comp (continuous_id.prodMk continuous_const).continuousOn fun x hx => ⟨hx, ht⟩
  -- a compact time window `[t₀ - ε, t₀ + ε]` inside `(0, T)`
  obtain ⟨ε, hε, hεT⟩ : ∃ ε > 0, Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo 0 T := by
    refine ⟨min t₀ (T - t₀) / 2, by have := ht₀.1; have := ht₀.2; positivity, ?_⟩
    intro s hs
    have h1 := min_le_left t₀ (T - t₀)
    have h2 := min_le_right t₀ (T - t₀)
    have h3 : 0 < min t₀ (T - t₀) := lt_min ht₀.1 (sub_pos.mpr ht₀.2)
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hball : Metric.ball t₀ ε ⊆ Icc (t₀ - ε) (t₀ + ε) := fun s hs => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨by linarith, by linarith⟩
  have hK : Icc a b ×ˢ Icc (t₀ - ε) (t₀ + ε) ⊆ Icc a b ×ˢ Ioo 0 T := prod_mono subset_rfl hεT
  -- a bound for the time derivative `2 w ∂ₜw` of the integrand on the window
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    ((continuousOn_const.mul (hw_cont.mono hK)).mul (hwt_cont.mono hK) :
      ContinuousOn (fun p : ℝ × ℝ => 2 * w p.1 p.2 * wt p.1 p.2) _)
  have hIoc : Ι a b = Ioc a b := uIoc_of_le hab.le
  have hmeas : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc a b) →
      AEStronglyMeasurable g (volume.restrict (Ι a b)) := fun hg => by
    rw [hIoc]
    exact (hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hint : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc a b) → IntervalIntegrable g volume a b :=
    fun hg => (uIcc_of_le hab.le ▸ hg).intervalIntegrable
  -- almost every point of `Ι a b` lies in `Ioo a b`
  have hIoo : ∀ᵐ x ∂volume, x ∈ Ι a b → x ∈ Ioo a b := by
    filter_upwards [(Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := b))] with x hx hxab
    rw [hIoc] at hxab
    exact hx.2 hxab
  -- differentiation under the integral sign
  have hleib := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => w x t ^ 2) (F' := fun t x => 2 * w x t * wt x t) (bound := fun _ => C)
    (Metric.ball_mem_nhds t₀ hε)
    (by
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
      exact hmeas ((slice hw_cont t ht).pow 2))
    (hint ((slice hw_cont t₀ ht₀).pow 2))
    (hmeas ((continuousOn_const.mul (slice hw_cont t₀ ht₀)).mul (slice hwt_cont t₀ ht₀)))
    (by
      refine ae_of_all _ fun x hx t hts => ?_
      rw [hIoc] at hx
      exact hC (x, t) ⟨Ioc_subset_Icc_self hx, hball hts⟩)
    intervalIntegrable_const
    (by
      filter_upwards [hIoo] with x hx hxab t hts
      convert (ht x (hx hxab) t (hεT (hball hts))).fun_pow 2 using 1
      ring)
  -- the diffusion equation and integration by parts at the time `t₀`
  have hibp := integral_mul_deriv_deriv_eq_neg hab.le (slice hw_cont t₀ ht₀)
    (slice hwx_cont t₀ ht₀) (slice hwxx_cont t₀ ht₀) (fun y hy => hx y hy t₀ ht₀)
    (fun y hy => hxx y hy t₀ ht₀) (hbc t₀ ht₀).1 (hbc t₀ ht₀).2
  have hpde' : ∫ x in a..b, 2 * w x t₀ * wt x t₀ = 2 * D * ∫ x in a..b, w x t₀ * wxx x t₀ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hIoo] with x hx hxab
    rw [hpde x (hx hxab) t₀ ht₀]
    ring
  convert hleib.2 using 1
  rw [hpde', hibp]
  ring

/-- **Uniqueness for the Dirichlet problem** (energy method). Let `w` equal `c₁ - c₂` on the
closed rectangle `[a, b] × [0, T]` and be continuous there; let `wx`, `wxx`, `wt` be continuous
on `[a, b] × (0, T)` and be the derivatives `∂ₓw`, `∂ₓₓw`, `∂ₜw` at the points of
`(a, b) × (0, T)`, where `∂ₜw = D ∂ₓₓw` with `D > 0`. If `w` vanishes at `x = a` and `x = b` for
`0 < t < T` and at `t = 0` on `[a, b]`, then `c₁ = c₂` on `[a, b] × [0, T]`. Nothing is assumed
outside the rectangle, so `c₁` and `c₂` may be solutions that exist only up to time `T`. -/
theorem diffusion_unique_dirichlet (a b T D : ℝ) (hab : a < b) (hD : 0 < D)
    (c₁ c₂ w wx wxx wt : ℝ → ℝ → ℝ)
    (hw_def : ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, w x t = c₁ x t - c₂ x t)
    (ht : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, HasDerivAt (fun τ => w x τ) (wt x t) t)
    (hx : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => w u t) (wx x t) x)
    (hxx : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => wx u t) (wxx x t) x)
    (hw_cont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc a b ×ˢ Icc 0 T))
    (hwx_cont : ContinuousOn (fun p : ℝ × ℝ => wx p.1 p.2) (Icc a b ×ˢ Ioo 0 T))
    (hwxx_cont : ContinuousOn (fun p : ℝ × ℝ => wxx p.1 p.2) (Icc a b ×ˢ Ioo 0 T))
    (hwt_cont : ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2) (Icc a b ×ˢ Ioo 0 T))
    (hpde : ∀ x ∈ Ioo a b, ∀ t ∈ Ioo 0 T, wt x t = D * wxx x t)
    (hbc : ∀ t ∈ Ioo 0 T, w a t = 0 ∧ w b t = 0)
    (hinit : ∀ x ∈ Icc a b, w x 0 = 0) :
    ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, c₁ x t = c₂ x t := by
  set E : ℝ → ℝ := fun t => ∫ x in a..b, w x t ^ 2 with hE_def
  have hE : ∀ t ∈ Ioo 0 T, HasDerivAt E (-2 * D * ∫ x in a..b, wx x t ^ 2) t := fun t ht' =>
    energy_identity_deriv hab (hw_cont.mono (prod_mono subset_rfl Ioo_subset_Icc_self))
      hwx_cont hwxx_cont hwt_cont ht hx hxx hpde hbc ht'
  -- the energy is nonincreasing on `[0, T]`
  have hanti : AntitoneOn E (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (continuousOn_energy hab.le hw_cont)
      (fun t ht' => ?_) fun t ht' => ?_
    · rw [interior_Icc] at ht'
      exact (hE t ht').differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht'
      rw [(hE t ht').deriv]
      have h0 : 0 ≤ ∫ x in a..b, wx x t ^ 2 :=
        intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _
      nlinarith
  -- the energy vanishes at `t = 0`, hence on `[0, T]`
  have hE0 : E 0 = 0 := by
    have h : EqOn (fun x => w x 0 ^ 2) (fun _ => (0 : ℝ)) (uIcc a b) := fun x hx => by
      rw [uIcc_of_le hab.le] at hx
      simp [hinit x hx]
    simp only [hE_def, intervalIntegral.integral_congr h, intervalIntegral.integral_zero]
  intro x hx t ht'
  have hEt : E t = 0 := le_antisymm (hE0 ▸ hanti ⟨le_rfl, ht'.1.trans ht'.2⟩ ht' ht'.1)
    (intervalIntegral.integral_nonneg hab.le fun y _ => sq_nonneg _)
  -- a nonzero value of the continuous `w (·) t` would make the energy positive
  by_contra hne
  have hw : w x t ≠ 0 := by rw [hw_def x hx t ht']; exact sub_ne_zero.mpr hne
  have hpos : 0 < E t := intervalIntegral.integral_pos hab
    ((hw_cont.comp (continuous_id.prodMk continuous_const).continuousOn
      fun y hy => ⟨hy, ht'⟩).pow 2) (fun _ _ => sq_nonneg _) ⟨x, hx, by positivity⟩
  linarith

/-!

## E. Parabolic scaling

-/

/-- The parabolic rescaling `(x, t) ↦ c(λx, λ²t)` of a field `c` (position, then time). -/
noncomputable def scaledSol (c : ℝ → ℝ → ℝ) (lam x t : ℝ) : ℝ :=
  c (lam * x) (lam ^ 2 * t)

/-- **Parabolic scaling at a point.** Suppose `c` has the time derivative `ct` at `(λx, λ²t)`, the
spatial derivative `cx` at every point of the line at time `λ²t`, and the second spatial
derivative `cxx` at `(λx, λ²t)`, and solves `∂ₜc = D ∂ₓₓc` there. Then the rescaling
`scaledSol c λ` solves the diffusion equation at `(x, t)`. Only the time `λ²t` enters, so this
applies to solutions defined for `t > 0` only, such as the Gaussian. -/
lemma similarity_pde_at (D lam : ℝ) (c cx cxx ct : ℝ → ℝ → ℝ) (x t : ℝ)
    (ht : HasDerivAt (fun σ => c (lam * x) σ) (ct (lam * x) (lam ^ 2 * t)) (lam ^ 2 * t))
    (hx : ∀ X, HasDerivAt (fun u => c u (lam ^ 2 * t)) (cx X (lam ^ 2 * t)) X)
    (hxx : HasDerivAt (fun u => cx u (lam ^ 2 * t)) (cxx (lam * x) (lam ^ 2 * t)) (lam * x))
    (hpde : ct (lam * x) (lam ^ 2 * t) = D * cxx (lam * x) (lam ^ 2 * t)) :
    deriv (fun τ => scaledSol c lam x τ) t
      = D * deriv (fun x' => deriv (fun u => scaledSol c lam u t) x') x := by
  have hTlin : HasDerivAt (fun τ => lam ^ 2 * τ) (lam ^ 2) t := by
    simpa using (hasDerivAt_id' t).const_mul (lam ^ 2)
  have hts : HasDerivAt (fun τ => scaledSol c lam x τ)
      (lam ^ 2 * ct (lam * x) (lam ^ 2 * t)) t := by
    have hraw := ht.comp t hTlin
    change HasDerivAt (fun τ => c (lam * x) (lam ^ 2 * τ))
      (lam ^ 2 * ct (lam * x) (lam ^ 2 * t)) t
    rw [mul_comm (lam ^ 2) (ct _ _)]
    exact hraw
  have hx1 : ∀ x' : ℝ, HasDerivAt (fun u => scaledSol c lam u t)
      (lam * cx (lam * x') (lam ^ 2 * t)) x' := by
    intro x'
    have hXlin : HasDerivAt (fun ξ => lam * ξ) lam x' := by
      simpa using (hasDerivAt_id' x').const_mul lam
    have hraw := (hx (lam * x')).comp x' hXlin
    change HasDerivAt (fun u => c (lam * u) (lam ^ 2 * t))
      (lam * cx (lam * x') (lam ^ 2 * t)) x'
    rw [mul_comm lam (cx _ _)]
    exact hraw
  have hxx2 : HasDerivAt (fun x' => deriv (fun u => scaledSol c lam u t) x')
      (lam * (lam * cxx (lam * x) (lam ^ 2 * t))) x := by
    have hfun : (fun x' => deriv (fun u => scaledSol c lam u t) x')
        = (fun x' => lam * cx (lam * x') (lam ^ 2 * t)) := by
      funext x'
      exact (hx1 x').deriv
    rw [hfun]
    have hXlin : HasDerivAt (fun ξ => lam * ξ) lam x := by
      simpa using (hasDerivAt_id' x).const_mul lam
    have hchain := (hxx.comp x hXlin).const_mul lam
    rw [mul_comm lam (cxx _ _)]
    exact hchain
  rw [hts.deriv, hxx2.deriv, hpde]
  ring

/-- **Parabolic scaling.** If `c` solves `∂ₜc = D ∂ₓₓc` on all of `ℝ × ℝ`, with the derivatives
`cx`, `cxx`, `ct` given at every point, then so does its rescaling `scaledSol c λ`. For a
solution on part of the plane, such as the Gaussian for `t > 0`, use `similarity_pde_at`. -/
theorem similarity_pde (D lam : ℝ) (_hlam : 0 < lam) (c cx cxx ct : ℝ → ℝ → ℝ)
    (ht : ∀ X T, HasDerivAt (fun σ => c X σ) (ct X T) T)
    (hx : ∀ X T, HasDerivAt (fun u => c u T) (cx X T) X)
    (hxx : ∀ X T, HasDerivAt (fun u => cx u T) (cxx X T) X)
    (hpde : ∀ X T, ct X T = D * cxx X T) :
    ∀ x t, deriv (fun τ => scaledSol c lam x τ) t
      = D * deriv (fun x' => deriv (fun u => scaledSol c lam u t) x') x :=
  fun x t => similarity_pde_at D lam c cx cxx ct x t (ht _ _) (fun X => hx X _) (hxx _ _)
    (hpde _ _)

/-- The similarity variable `ξ = x / √(Dt)`. It is meant for `D > 0` and `t > 0`; when
`D t ≤ 0` the square root is `0` and the value is `0` by Lean's division convention. -/
noncomputable def simVar (D x t : ℝ) : ℝ :=
  x / Real.sqrt (D * t)

/-- The similarity variable is invariant under parabolic scaling:
`simVar D (λx) (λ²t) = simVar D x t` for `D > 0`, `t > 0` and `λ > 0`. -/
lemma simVar_invariant (D x t lam : ℝ) (hD : 0 < D) (ht : 0 < t) (hlam : 0 < lam) :
    simVar D (lam * x) (lam ^ 2 * t) = simVar D x t := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hDt : (0 : ℝ) < D * t := by positivity
  have hsq : Real.sqrt (D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hDt)
  have hsqrt : Real.sqrt (D * (lam ^ 2 * t)) = lam * Real.sqrt (D * t) := by
    have hfactor : (D * (lam ^ 2 * t) : ℝ) = lam ^ 2 * (D * t) := by ring
    rw [hfactor, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam.le]
  simp only [simVar]
  rw [hsqrt]
  field_simp

/-!

## F. The steady membrane profile

-/

/-- The linear steady profile on `[0, L]` from `c₁` at `x = 0` to `c₂` at `x = L`:
`c₁ + (c₂ - c₁) x / L`. It is meant for `L > 0`; for `L = 0` the slope `(c₂ - c₁) / 0` is `0` and
the profile is the constant `c₁`. -/
noncomputable def steadyProfile (c₁ c₂ L x : ℝ) : ℝ :=
  c₁ + ((c₂ - c₁) / L) * x

/-- The steady profile takes the value `c₁` at `x = 0`. -/
lemma steady_boundary_zero (c₁ c₂ L : ℝ) : steadyProfile c₁ c₂ L 0 = c₁ := by
  simp only [steadyProfile, mul_zero, add_zero]

/-- For `L > 0`, the steady profile takes the value `c₂` at `x = L`. -/
lemma steady_boundary_L (c₁ c₂ L : ℝ) (hL : 0 < L) : steadyProfile c₁ c₂ L L = c₂ := by
  have hL' : L ≠ 0 := ne_of_gt hL
  simp only [steadyProfile]
  field_simp
  ring

/-- The steady profile has the constant slope `(c₂ - c₁) / L`. -/
lemma steady_xderiv_value (c₁ c₂ L x : ℝ) :
    HasDerivAt (fun x => steadyProfile c₁ c₂ L x) (((c₂ - c₁) / L) * 1) x := by
  have hmul : HasDerivAt (fun x : ℝ => ((c₂ - c₁) / L) * x) (((c₂ - c₁) / L) * 1) x := by
    simpa using (hasDerivAt_id' x).const_mul ((c₂ - c₁) / L)
  simpa [steadyProfile] using hmul.const_add c₁

/-- The steady profile solves the steady diffusion equation: it does not depend on time, and
`D ∂ₓₓc = 0`. -/
lemma steady_pde (c₁ c₂ L D x t : ℝ) (_hL : 0 < L) :
    deriv (fun _ => steadyProfile c₁ c₂ L x) t = 0
      ∧ D * deriv (fun x' => deriv (fun u => steadyProfile c₁ c₂ L u) x') x = 0 := by
  constructor
  · exact deriv_const _ _
  · have hfun : (fun x' => deriv (fun u => steadyProfile c₁ c₂ L u) x')
        = (fun _ => ((c₂ - c₁) / L) * 1) := by
      funext x'
      exact (steady_xderiv_value c₁ c₂ L x').deriv
    rw [hfun]
    have h0 : deriv (fun _ : ℝ => ((c₂ - c₁) / L) * 1) x = 0 := deriv_const _ _
    rw [h0, mul_zero]

/-- **Steady membrane flux.** For `L > 0`, the Fick flux of the steady profile is
`D (c₁ - c₂) / L` at every `x`. -/
theorem steady_flux (c₁ c₂ L D : ℝ) (hL : 0 < L) (x : ℝ) :
    -D * deriv (fun x' => steadyProfile c₁ c₂ L x') x = D * (c₁ - c₂) / L := by
  have hL' : L ≠ 0 := ne_of_gt hL
  rw [(steady_xderiv_value c₁ c₂ L x).deriv]
  field_simp
  ring

/-!

## G. The slab sine series

-/

/-- The sine coefficients `bₙ = 2c₀ (1 - (-1)ⁿ) / (nπ)` of the uniform initial profile `c₀` on
`[0, L]`, with `b₀ = 0`: `4c₀ / (nπ)` for odd `n` and `0` for even `n`. They do not depend on the
width `L`, which is a parameter only so that `fourierCoeff c₀ L` and `fourierTerm c₀ L D` take the
same arguments. `fourierCoeff_formula` identifies them with `(2/L) ∫₀ᴸ c₀ sin(nπx/L) dx` for
`L > 0` and `n ≥ 1`. -/
noncomputable def fourierCoeff (c₀ _L : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (2 * c₀ / (n * Real.pi)) * (1 - (-1) ^ n)

/-- The `n`-th term `bₙ sin(nπx/L) exp(-D (nπ/L)² t)` of the sine series for diffusion in the
slab `[0, L]` with zero Dirichlet values and the uniform initial concentration `c₀`. It is meant
for `L > 0`; for `L = 0` the divisions by `L` give `0` and the term is `0`. -/
noncomputable def fourierTerm (c₀ L D : ℝ) (n : ℕ) (x t : ℝ) : ℝ :=
  fourierCoeff c₀ L n * Real.sin (n * Real.pi * x / L)
    * Real.exp (-D * (n * Real.pi / L) ^ 2 * t)

/-- **Sine coefficients of a uniform profile.** For `L > 0` and `n ≥ 1`,
`(2/L) ∫₀ᴸ c₀ sin(nπx/L) dx = fourierCoeff c₀ L n`: `4c₀ / (nπ)` for odd `n` and `0` for even
`n`. -/
theorem fourierCoeff_formula (c₀ L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    (2 / L) * ∫ x in (0 : ℝ)..L, c₀ * Real.sin (n * Real.pi * x / L)
      = fourierCoeff c₀ L n := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by
    have h0n : 0 < n := by omega
    exact_mod_cast h0n
  have hnpi : (0 : ℝ) < n * Real.pi := mul_pos hnpos Real.pi_pos
  have hnpi' : (n * Real.pi : ℝ) ≠ 0 := ne_of_gt hnpi
  have hform : (fun x : ℝ => n * Real.pi * x / L) = (fun x => (n * Real.pi / L) * x) := by
    funext x
    ring
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) L, HasDerivAt
      (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x))
      (c₀ * Real.sin ((n * Real.pi / L) * x)) x := by
    intro x _
    have hu : HasDerivAt (fun x : ℝ => (n * Real.pi / L) * x) ((n * Real.pi) / L) x := by
      simpa using (hasDerivAt_id' x).const_mul ((n * Real.pi) / L)
    have hcos := hu.cos
    have hchain := hcos.const_mul (c₀ * (-L / (n * Real.pi)))
    change HasDerivAt (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x))
      (c₀ * Real.sin ((n * Real.pi / L) * x)) x
    have hder : c₀ * Real.sin ((n * Real.pi / L) * x)
        = c₀ * (-L / (n * Real.pi))
          * (-Real.sin ((n * Real.pi / L) * x) * ((n * Real.pi) / L)) := by
      field_simp
    rw [hder]
    exact hchain
  have hFcont : ContinuousOn (fun x => c₀ * Real.sin ((n * Real.pi / L) * x)) (Set.uIcc 0 L) := by
    have hsin : Continuous (fun x : ℝ => Real.sin ((n * Real.pi / L) * x)) :=
      Real.continuous_sin.comp (continuous_id.const_mul _)
    have hmul := hsin.const_mul c₀
    exact hmul.continuousOn
  have hFint : IntervalIntegrable (fun x => c₀ * Real.sin ((n * Real.pi / L) * x)) volume 0 L :=
    hFcont.intervalIntegrable
  have hFTC : (∫ x in (0 : ℝ)..L, c₀ * Real.sin ((n * Real.pi / L) * x))
      = (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x)) L
        - (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x)) 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hF hFint
  have hcosL : Real.cos ((n * Real.pi / L) * L) = (-1) ^ n := by
    have harg : (n * Real.pi / L) * L = n * Real.pi := by
      field_simp
    rw [harg]
    exact Real.cos_nat_mul_pi n
  have hcos0 : Real.cos ((n * Real.pi / L) * 0) = 1 := by
    have harg : (n * Real.pi / L) * 0 = 0 := by ring
    rw [harg]
    exact Real.cos_zero
  simp only [fourierCoeff, ite_eq_right hn0]
  have harg : ∀ x : ℝ, (n * Real.pi * x / L) = ((n * Real.pi / L) * x) :=
    fun x => congrFun hform x
  simp_rw [harg]
  rw [hFTC]
  simp only []
  rw [hcosL, hcos0]
  field_simp
  ring

/-- For `c₀ ≥ 0`, `L > 0`, `D > 0` and `t ≥ δ > 0`, the `n`-th term is bounded by
`(4c₀/π + 1) ρⁿ` with `ρ = exp(-D (π/L)² δ)`, uniformly in `x`. -/
lemma fourierTerm_bound (c₀ L D δ : ℝ) (hc₀ : 0 ≤ c₀) (hL : 0 < L) (hD : 0 < D) (hδ : 0 < δ)
    (n : ℕ) (x t : ℝ) (ht : δ ≤ t) :
    ‖fourierTerm c₀ L D n x t‖
      ≤ (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hn0 : n = 0
  · subst hn0
    have hb0 : fourierCoeff c₀ L 0 = 0 := ite_eq_left rfl
    have hC : (0 : ℝ) ≤ 4 * c₀ / Real.pi + 1 := by positivity
    simp only [fourierTerm, hb0, zero_mul, norm_zero, pow_zero, mul_one]
    exact hC
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnR : (0 : ℝ) < n := by
      have h0n : 0 < n := by omega
      exact_mod_cast h0n
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpi' : (n * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos hnR Real.pi_pos)
    have h3 : (0 : ℝ) ≤ 4 * c₀ / (n * Real.pi) := by positivity
    have h2n : (0 : ℝ) ≤ 2 * c₀ / (n * Real.pi) := by positivity
    have hb : |fourierCoeff c₀ L n| ≤ 4 * c₀ / (n * Real.pi) := by
      simp only [fourierCoeff, ite_eq_right hn0]
      have h1 : |(-1 : ℝ) ^ n| = 1 := by
        rw [abs_pow, abs_neg, abs_one, one_pow]
      have h2 : |(1 : ℝ) - (-1) ^ n| ≤ 2 := by
        calc |(1 : ℝ) - (-1) ^ n| = |1 + (-(-1) ^ n)| := by rw [sub_eq_add_neg]
          _ ≤ |1| + |-(-1) ^ n| := abs_add_le _ _
          _ = 2 := by rw [abs_one, abs_neg, h1]; norm_num
      calc |(2 * c₀ / (n * Real.pi)) * (1 - (-1) ^ n)|
          = |2 * c₀ / (n * Real.pi)| * |1 - (-1) ^ n| := abs_mul _ _
        _ = (2 * c₀ / (n * Real.pi)) * |1 - (-1) ^ n| := by rw [abs_of_nonneg h2n]
        _ ≤ (2 * c₀ / (n * Real.pi)) * 2 := mul_le_mul_of_nonneg_left h2 h2n
        _ = 4 * c₀ / (n * Real.pi) := by
            field_simp
            ring
    have hsin : |Real.sin (n * Real.pi * x / L)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have hexp_t : Real.exp (-D * (n * Real.pi / L) ^ 2 * t)
        ≤ Real.exp (-D * (n * Real.pi / L) ^ 2 * δ) := by
      apply Real.exp_le_exp.mpr
      have hnn : (-D * (n * Real.pi / L) ^ 2) ≤ 0 := by
        have h1 : (0 : ℝ) ≤ D * (n * Real.pi / L) ^ 2 := mul_nonneg hD.le (sq_nonneg _)
        have h2 : -D * (n * Real.pi / L) ^ 2 = -(D * (n * Real.pi / L) ^ 2) := by ring
        rw [h2]
        linarith [h1]
      exact mul_le_mul_of_nonpos_left ht hnn
    have hexp_n : Real.exp (-D * (n * Real.pi / L) ^ 2 * δ)
        ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
      have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith [sq_nonneg ((n : ℝ) - 1), hn1']
      have hk : (0 : ℝ) ≤ D * (Real.pi / L) ^ 2 * δ :=
        mul_nonneg (mul_nonneg hD.le (sq_nonneg _)) hδ.le
      have hX : (-D * (n * Real.pi / L) ^ 2 * δ) ≤ n * (-D * (Real.pi / L) ^ 2 * δ) := by
        have hsq : (n * Real.pi / L) ^ 2 = (n : ℝ) ^ 2 * (Real.pi / L) ^ 2 := by
          ring
        rw [hsq]
        nlinarith [mul_nonneg (sub_nonneg.mpr hn2) hk]
      calc Real.exp (-D * (n * Real.pi / L) ^ 2 * δ)
          ≤ Real.exp (n * (-D * (Real.pi / L) ^ 2 * δ)) := Real.exp_le_exp.mpr hX
        _ = Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := Real.exp_nat_mul _ _
    have hexp_le : Real.exp (-D * (n * Real.pi / L) ^ 2 * t)
        ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := hexp_t.trans hexp_n
    have hρ0 : (0 : ℝ) ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by positivity
    have g1 := hb
    have g2 := hsin
    have g3 : (0 : ℝ) ≤ |Real.sin (n * Real.pi * x / L)| := abs_nonneg _
    have g4 := h3
    have h12 : |fourierCoeff c₀ L n| * |Real.sin (n * Real.pi * x / L)|
        ≤ (4 * c₀ / (n * Real.pi)) * 1 := by
      apply mul_le_mul <;> assumption
    have g5 : (0 : ℝ) ≤ Real.exp (-D * (n * Real.pi / L) ^ 2 * t) := (Real.exp_pos _).le
    have g6 : (0 : ℝ) ≤ (4 * c₀ / (n * Real.pi)) * 1 := mul_nonneg h3 zero_le_one
    have h123 : (|fourierCoeff c₀ L n| * |Real.sin (n * Real.pi * x / L)|)
        * Real.exp (-D * (n * Real.pi / L) ^ 2 * t)
        ≤ ((4 * c₀ / (n * Real.pi)) * 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
      apply mul_le_mul <;> assumption
    have hCbound : (4 * c₀ / (n * Real.pi)) * 1 ≤ 4 * c₀ / Real.pi + 1 := by
      rw [mul_one]
      have hle : 4 * c₀ / (n * Real.pi) ≤ 4 * c₀ / Real.pi := by
        have heq : (4 * c₀ / (n * Real.pi)) = (4 * c₀ / Real.pi) * (1 / n) := by
          field_simp
        rw [heq]
        have h1n : (1 : ℝ) / n ≤ 1 := (div_le_one hnR).mpr hn1R
        have hnn : (0 : ℝ) ≤ 4 * c₀ / Real.pi := by positivity
        calc (4 * c₀ / Real.pi) * (1 / n) ≤ (4 * c₀ / Real.pi) * 1 :=
              mul_le_mul_of_nonneg_left h1n hnn
          _ = 4 * c₀ / Real.pi := mul_one _
      linarith [hle]
    have hfinal : ((4 * c₀ / (n * Real.pi)) * 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n
        ≤ (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n :=
      mul_le_mul_of_nonneg_right hCbound hρ0
    simp only [fourierTerm]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    exact le_trans h123 hfinal

/-- The bounds `(4c₀/π + 1) ρⁿ` of `fourierTerm_bound` are summable, since
`ρ = exp(-D (π/L)² δ) < 1`. -/
lemma fourier_dominator_summable (c₀ L D δ : ℝ) (hL : 0 < L) (hD : 0 < D) (hδ : 0 < δ) :
    Summable (fun n : ℕ =>
      (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n) := by
  have hρ0 : (0 : ℝ) ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-D * (Real.pi / L) ^ 2 * δ) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have hL' : L ≠ 0 := ne_of_gt hL
    have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
    have hpl : (Real.pi / L : ℝ) ≠ 0 := div_ne_zero hpi' hL'
    have hsq2 : (Real.pi / L) ^ 2 ≠ 0 := by
      rw [pow_two]
      exact mul_ne_zero hpl hpl
    have hsq : (0 : ℝ) < (Real.pi / L) ^ 2 := lt_of_le_of_ne (sq_nonneg _) hsq2.symm
    have hDL : (0 : ℝ) < D * (Real.pi / L) ^ 2 * δ :=
      mul_pos (mul_pos hD hsq) hδ
    linarith
  have hgeom := summable_geometric_of_lt_one hρ0 hρ1
  exact hgeom.mul_left _

/-- **Uniform convergence of the slab series.** For `c₀ ≥ 0`, `L > 0`, `D > 0` and `δ > 0`, the
partial sums `∑_{n < N} fourierTerm c₀ L D n x t` converge to the sum of the series uniformly on
`[0, L] × [δ, ∞)` (Weierstrass M-test). That the sum solves the diffusion equation or attains
the initial data at `t = 0` is not proved. -/
theorem fourier_uniform_convergent (c₀ L D δ : ℝ) (hc₀ : 0 ≤ c₀) (hL : 0 < L) (hD : 0 < D)
    (hδ : 0 < δ) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℝ × ℝ => (Finset.range N).sum fun n => fourierTerm c₀ L D n p.1 p.2)
      (fun p => ∑' n, fourierTerm c₀ L D n p.1 p.2) atTop
      (Set.Icc 0 L ×ˢ Set.Ici δ) := by
  have hM := fourier_dominator_summable c₀ L D δ hL hD hδ
  have hbdd : ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ Set.Icc 0 L ×ˢ Set.Ici δ →
      ‖fourierTerm c₀ L D n p.1 p.2‖
        ≤ (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
    intro n p hp
    have ht : δ ≤ p.2 := Set.mem_Ici.mp (mem_prod.mp hp).2
    exact fourierTerm_bound c₀ L D δ hc₀ hL hD hδ n p.1 p.2 ht
  exact tendstoUniformlyOn_tsum_nat hM hbdd

end CondensedMatter.Diffusion

end
