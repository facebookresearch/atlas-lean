/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# Conservative and advective forms of advection-diffusion-reaction

In one spatial dimension, the conservative
advection-diffusion-reaction equation is
`c_t + d/dx (U * c - D * c_x) = -k * c`, where `U` is the carrier
velocity, `D` the diffusivity, `k` the reaction rate, and the flux is
`J = U * c - D * c_x`. The advective form is
`c_t + U * c_x - D * c_xx = -k * c`. The two forms agree at a point
where the carrier velocity satisfies the continuity equation
`d/dx U = 0` (divergence-free / incompressible carrier in one
dimension): there `d/dx (U * c) = U * c_x` by the product rule, since
the `c * U_x` term vanishes. Without continuity the product rule leaves
the extra term `c * U_x`.

## i. Overview

The flux-divergence identity follows from `HasDerivAt.mul` (with the
continuity hypothesis) and `HasDerivAt.const_mul`. The PDE-form
equivalence applies the identity at a single point `(t, x)` and assumes
regularity of `C t` only at `x`.

## ii. Key results

- `EarthScience.flux_divergence_eq_advective`: at a point, the flux
  divergence equals the advective operator under continuity.
- `EarthScience.conservative_advective_pde_equiv`: at a point `(t, x)`,
  the conservative and advective PDE forms are equivalent under
  continuity.

## iii. Table of contents

- A. Flux divergence and PDE-form equivalence

## iv. References

- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*,
  Cambridge University Press, 2002, Chapter 2: the integral
  conservation law and the advection-diffusion flux
  `u q - beta q_x`.
- `HasDerivAt.mul`, `HasDerivAt.const_mul` in Mathlib.

## A. Flux divergence and PDE-form equivalence
-/

@[expose] public section

namespace EarthScience

/-- Conservative and advective forms agree at a point: if the carrier
velocity satisfies the 1-D continuity equation `∂ₓU = 0` at `x`
(`HasDerivAt U 0 x`) and `c` and `cₓ` are differentiable at `x`, then
the divergence of the flux `J = U * c - D * cₓ` at `x` equals the
advective operator `U * cₓ - D * cₓₓ` at `x`. -/
theorem flux_divergence_eq_advective (U c : ℝ → ℝ) (D x : ℝ)
    (hU : HasDerivAt U 0 x)
    (hc1 : HasDerivAt c (deriv c x) x)
    (hc2 : HasDerivAt (fun x => deriv c x) (deriv (fun x => deriv c x) x) x) :
    deriv (fun x => U x * c x - D * deriv c x) x =
      U x * deriv c x - D * deriv (fun x => deriv c x) x := by
  have hmul := hU.fun_mul hc1
  have hcmul := hc2.const_mul D
  have hsub := hmul.fun_sub hcmul
  have hderiv := hsub.deriv
  simpa using hderiv

/-- PDE-form equivalence at a point: if `∂ₓU = 0` at `x` and `C t` and
its spatial derivative are differentiable at `x`, the conservative
advection-diffusion-reaction equation `cₜ + ∂ₓ(U c - D cₓ) = -k c`
holds at `(t, x)` iff the advective form `cₜ + U cₓ - D cₓₓ = -k c`
holds there. Regularity is assumed only at the point considered. -/
theorem conservative_advective_pde_equiv (U : ℝ → ℝ) (C : ℝ → ℝ → ℝ)
    (D k t x : ℝ)
    (hU : HasDerivAt U 0 x)
    (hc1 : HasDerivAt (fun x => C t x) (deriv (fun x => C t x) x) x)
    (hc2 : HasDerivAt (fun x => deriv (fun x => C t x) x)
      (deriv (fun x => deriv (fun x => C t x) x) x) x) :
    (deriv (fun t => C t x) t +
        deriv (fun x => U x * C t x - D * deriv (fun x => C t x) x) x =
          -k * C t x) ↔
    (deriv (fun t => C t x) t + U x * deriv (fun x => C t x) x -
        D * deriv (fun x => deriv (fun x => C t x) x) x = -k * C t x) := by
  have h := flux_divergence_eq_advective U (fun x => C t x) D x hU hc1 hc2
  rw [h]
  constructor <;> intro h' <;> linarith

end EarthScience
