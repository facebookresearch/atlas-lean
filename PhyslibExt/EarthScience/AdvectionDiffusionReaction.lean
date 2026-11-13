/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-!
# Advection, diffusion, and reaction: mass balance

For constant carrier velocity `U`, diffusivity `D` and decay rate `k`,
a tracer obeying `c_t + U c_x = D c_xx - k c` between `a` and `b`
satisfies `d/dt ∫ x in a..b, c = J(a) - J(b) - k ∫ x in a..b, c` with
flux `J = U c - D c_x`. No zero-flux boundary is assumed.

## i. Overview

Integrating the PDE from `a` to `b`: the `D c_xx` term integrates by the
fundamental theorem of calculus to `D (c_x(b) - c_x(a))`, and the
advection term integrates to `U (c(b) - c(a))` using `HasDerivAt` of `c`
in `x` (the `hx_deriv` hypothesis). The PDE and both spatial derivative
hypotheses are assumed only on `Set.uIcc a b`. The derivative form
assumes differentiation under the integral sign (`hswap`) as an explicit
hypothesis.

The integrals are oriented interval integrals, so the balance is a signed
identity. For `a ≤ b` it is the physical balance on `[a, b]`: the mass
`∫ x in a..b, c` changes by the net inflow `J(a) - J(b)` minus the decay
term. For `b < a` both sides are the negatives of the balance on `[b, a]`.
The identity holds for all real `U`, `D`, `k` and every concentration; its
reading as diffusion and decay of a tracer amount needs `0 ≤ D`, `0 ≤ k`
and `0 ≤ c`.

## ii. Key results

- `EarthScience.integrated_advection_diffusion_reaction`: the integrated
  signed balance for `∫ c_t`.
- `EarthScience.mass_balance_advection_diffusion_reaction`: the derivative
  of the signed mass `∫ x in a..b, c`.

## iii. Table of contents

- A. Integrated balance and mass balance

## iv. References

- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge
  University Press, 2002, Chapter 2. Eq. (2.2) is the integral conservation
  law `d/dt ∫_{x₁}^{x₂} q dx = F₁(t) - F₂(t)`, with `F₁` and `-F₂` the
  fluxes into the section through its endpoints. In §2.2 the flux
  `ū q - β q_x` (advection plus Fick's law, Eq. (2.20)) gives the
  advection-diffusion equation `q_t + ū q_x = β q_xx` (Eq. (2.23)). §2.5
  adds a source density `ψ`, giving `q_t + f(q)_x = ψ` (Eq. (2.28)); §2.5.2
  uses the decay source `-α q₁` for an advected tracer (Eq. (2.29)) and the
  reaction-advection-diffusion form `q_t + A q_x = β q_xx + ψ(q)`
  (Eq. (2.30)). Here `ū = U`, `β = D`, `ψ = -k c`, and the flux is
  `J = U c - D c_x`.
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` in
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
  (Mathlib).

## A. Integrated balance and mass balance
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

/-- Integrated advection-diffusion-reaction balance at time `t`. Let
`c t x` be a tracer concentration, `U` the constant carrier velocity,
`D` the diffusivity and `k` the decay rate, with flux
`J t x = U * c t x - D * ∂ₓ c t x`. If the PDE
`∂ₜc + U ∂ₓc = D ∂ₓₓc - k c` holds at every point of `Set.uIcc a b`
(derivatives written with `deriv`) and the needed interval integrals
exist, then the oriented integral of `∂ₜc` from `a` to `b` equals
`J(t, a) - J(t, b) - k ∫ x in a..b, c t x`. For `a ≤ b` this is the net
inflow into `[a, b]` minus the decayed amount; for `b < a` both sides are
the negatives of the balance on `[b, a]`. The identity holds for all real
`U`, `D`, `k` and concentrations; the diffusion and decay reading needs
`0 ≤ D`, `0 ≤ k` and `0 ≤ c`. -/
theorem integrated_advection_diffusion_reaction (c : ℝ → ℝ → ℝ) (U D k a b t : ℝ)
    (hpde : ∀ x ∈ Set.uIcc a b,
      deriv (fun t => c t x) t + U * deriv (fun x => c t x) x =
        D * deriv (fun x => deriv (fun x' => c t x') x) x - k * c t x)
    (hxx_int : IntervalIntegrable
      (fun x => deriv (fun x => deriv (fun x' => c t x') x) x) MeasureTheory.volume a b)
    (hx_int : IntervalIntegrable (fun x => deriv (fun x => c t x) x)
      MeasureTheory.volume a b)
    (hc_int : IntervalIntegrable (fun x => c t x) MeasureTheory.volume a b)
    (hxx_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => deriv (fun x' => c t x') x)
      (deriv (fun x => deriv (fun x' => c t x') x) x) x)
    (hx_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => c t x)
      (deriv (fun x => c t x) x) x) :
    (∫ x in a..b, deriv (fun t => c t x) t) =
      (U * c t a - D * deriv (fun x => c t x) a) -
        (U * c t b - D * deriv (fun x => c t x) b) - k * ∫ x in a..b, c t x := by
  have hftc_xx : (∫ x in a..b, deriv (fun x => deriv (fun x' => c t x') x) x) =
      deriv (fun x => c t x) b - deriv (fun x => c t x) a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hxx_deriv hxx_int
  have hftc_x : (∫ x in a..b, deriv (fun x => c t x) x) = c t b - c t a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hx_deriv hx_int
  have hpt : ∀ x ∈ Set.uIcc a b, deriv (fun t => c t x) t =
      D * deriv (fun x => deriv (fun x' => c t x') x) x - k * c t x -
        U * deriv (fun x => c t x) x := by
    intro x hx
    have h := hpde x hx
    linarith
  have hcongr : (∫ x in a..b, deriv (fun t => c t x) t) =
      ∫ x in a..b, (D * deriv (fun x => deriv (fun x' => c t x') x) x - k * c t x -
        U * deriv (fun x => c t x) x) :=
    intervalIntegral.integral_congr fun x hx => hpt x hx
  have hD : IntervalIntegrable
      (fun x => D * deriv (fun x => deriv (fun x' => c t x') x) x)
      MeasureTheory.volume a b :=
    hxx_int.const_mul D
  have hk : IntervalIntegrable (fun x => k * c t x) MeasureTheory.volume a b :=
    hc_int.const_mul k
  have hU : IntervalIntegrable (fun x => U * deriv (fun x => c t x) x)
      MeasureTheory.volume a b :=
    hx_int.const_mul U
  rw [hcongr, intervalIntegral.integral_sub (hD.sub hk) hU,
    intervalIntegral.integral_sub hD hk, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hftc_xx, hftc_x]
  ring



/-- Mass balance: the time derivative of the signed mass
`∫ x in a..b, c t x` equals `J(t, a) - J(t, b) - k ∫ x in a..b, c t x`,
assuming differentiation under the integral sign (the derivative of the
integral is the integral of `∂ₜc`). For `a ≤ b` this is the total mass on
`[a, b]`, changing by net inflow minus decay; for `b < a` both sides are
the negatives of the balance on `[b, a]`. The decay reading needs
`0 ≤ D`, `0 ≤ k` and `0 ≤ c`. -/
theorem mass_balance_advection_diffusion_reaction (c : ℝ → ℝ → ℝ) (U D k a b t : ℝ)
    (hpde : ∀ x ∈ Set.uIcc a b,
      deriv (fun t => c t x) t + U * deriv (fun x => c t x) x =
        D * deriv (fun x => deriv (fun x' => c t x') x) x - k * c t x)
    (hxx_int : IntervalIntegrable
      (fun x => deriv (fun x => deriv (fun x' => c t x') x) x) MeasureTheory.volume a b)
    (hx_int : IntervalIntegrable (fun x => deriv (fun x => c t x) x)
      MeasureTheory.volume a b)
    (hc_int : IntervalIntegrable (fun x => c t x) MeasureTheory.volume a b)
    (hxx_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => deriv (fun x' => c t x') x)
      (deriv (fun x => deriv (fun x' => c t x') x) x) x)
    (hx_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => c t x)
      (deriv (fun x => c t x) x) x)
    (hswap : HasDerivAt (fun t => ∫ x in a..b, c t x)
      (∫ x in a..b, deriv (fun t => c t x) t) t) :
    HasDerivAt (fun t => ∫ x in a..b, c t x)
      ((U * c t a - D * deriv (fun x => c t x) a) -
        (U * c t b - D * deriv (fun x => c t x) b) - k * ∫ x in a..b, c t x) t := by
  have h1 := integrated_advection_diffusion_reaction c U D k a b t hpde
    hxx_int hx_int hc_int hxx_deriv hx_deriv
  rwa [h1] at hswap

end EarthScience
