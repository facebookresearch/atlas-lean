/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Graduate quasigeostrophic conservation

For quasigeostrophic potential vorticity
`q = Delta psi - psi / Ld^2 + beta * y` with `q_t + J(psi, q) = 0`,
energy `E = 0.5 * integral (|grad psi|^2 + psi^2 / Ld^2)` and
enstrophy `0.5 * integral q^2` are conserved in the channel with
`Lx`-periodic `x` and `psi = 0` walls. This module proves the pointwise
divergence-form identities that carry the conservation, with the partial
derivatives entered as real values: the enstrophy flux divergence is
`q * J(psi, q)`, and, using the QG equation, the energy-density time
derivative is the divergence of
`G = psi * grad psi_t + (psi^2 / 2 * q_y, -psi^2 / 2 * q_x)`.
Integrated over the channel, the flux divergences are boundary terms
vanishing under the stated periodic / wall conditions; that
integration by the divergence theorem is documented here, not
formalized as a separate integral theorem. Conditional identities
only: no PDE existence is claimed.

## i. Overview

The Jacobian is antisymmetric with `J(a, a) = 0`. The enstrophy flux
`(-psi_y * q^2 / 2, psi_x * q^2 / 2)` has divergence `q * J(psi, q)`,
so `d/dt (q^2 / 2) = -q * J(psi, q)` is in divergence form.

For energy, `e_t = div (psi * grad psi_t) - psi * q_t`, because
`beta * y` does not depend on time. The QG equation `q_t = -J(psi, q)`
turns `-psi * q_t` into `psi * J(psi, q)`, the divergence of
`(psi^2 / 2 * q_y, -psi^2 / 2 * q_x)`. On the walls `psi = 0`, so both
`y`-components `psi * psi_yt` and `-psi^2 / 2 * q_x` of `G` vanish there.

`energy_flux_divergence` is a different, flux `psi_t * grad psi`, form of
`e_t`. Its residual `-psi_t * q + beta * y * psi_t` is not a divergence,
so that form alone does not give conservation.

A Jacobian whose two `x`-derivatives vanish is zero; no particular
streamfunction is formalized.

## ii. Key results

- `EarthScience.jacobian_antisymm_self`: Jacobian antisymmetry and diagonal.
- `EarthScience.enstrophy_flux_divergence`: enstrophy flux divergence.
- `EarthScience.energy_flux_divergence`: the `psi_t * grad psi` form of `e_t`.
- `EarthScience.energy_density_rate_eq`: `e_t = div (psi * grad psi_t) - psi * q_t`.
- `EarthScience.psi_mul_jacobian_eq_div`: `psi * J(psi, q)` is a divergence.
- `EarthScience.energy_flux_divergence_of_qg`: with `q_t = -J(psi, q)`,
  `e_t = div G`.
- `EarthScience.jacobian_eq_zero_of_x_derivs_eq_zero`: `psi_x = q_x = 0`
  gives `J(psi, q) = 0`.

## iii. Table of contents

- A. Quasigeostrophic conservation identities

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics: Fundamentals and
  Large-Scale Circulation*, 2nd ed., Cambridge University Press (2017),
  Chapter 5: §5.3, the single-layer shallow water quasi-geostrophic
  equations (potential vorticity `Delta psi + beta * y - psi / Ld^2`
  advected by the geostrophic flow), and §5.6, the energetics of
  quasi-geostrophy (energy and enstrophy conservation).
- `ring` / `field_simp` in Mathlib (all identities are polynomial
  identities once the denominators `Ld^2` are cleared).
-/

@[expose] public section

namespace EarthScience


/-- Jacobian `J(a, b) = a_x * b_y - a_y * b_x` (with `a_x, a_y, b_x, b_y`
the partial-derivative values) is antisymmetric and vanishes on the
diagonal: `J(a, b) = -J(b, a)` and `J(a, a) = 0`. -/
theorem jacobian_antisymm_self {ax ay bx byy : ℝ} :
    (ax * byy - ay * bx) = -(bx * ay - byy * ax) ∧ (ax * ay - ay * ax) = 0 := by
  constructor <;> ring

/-- Enstrophy flux divergence: for `q` with partials `q_x, q_y` and
`psi` with partials `psi_x, psi_y, psi_xy`, the flux
`F = (-psi_y * q^2 / 2, psi_x * q^2 / 2)` has divergence
`q * J(psi, q)`. Hence `d/dt (q^2 / 2) = -q * J(psi, q)` is in
divergence form: integrated over the channel it reduces to boundary
terms, which vanish for periodic-in-`x` and wall (`psi = 0`) conditions. -/
theorem enstrophy_flux_divergence {psi_x psi_y psi_xy q q_x q_y : ℝ} :
    (-psi_xy * q ^ 2 / 2 - psi_y * q * q_x) +
      (psi_xy * q ^ 2 / 2 + psi_x * q * q_y) =
      q * (psi_x * q_y - psi_y * q_x) := by
  ring

set_option linter.unusedVariables false in
/-- Energy-density identity in the flux `psi_t * grad psi` form: with
`e_t = psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld^2` the time
derivative of the energy density `0.5 * (|grad psi|^2 + psi^2 / Ld^2)`,
and `div (psi_t * grad psi) = psi_t * (psi_xx + psi_yy) + psi_xt * psi_x +
psi_yt * psi_y`, one has
`e_t = div (psi_t * grad psi) - psi_t * ((psi_xx + psi_yy) - psi / Ld^2)`,
that is `e_t = div - psi_t * q + beta * y * psi_t`. The residual is not a
divergence, and the channel boundary conditions do not remove
`beta * y * psi_t`, so this form alone does not give energy conservation;
`energy_flux_divergence_of_qg` is the conservation identity. -/
theorem energy_flux_divergence {psi psi_x psi_y psi_t psi_xt psi_yt psi_xx psi_yy Ld : ℝ}
    (hLd : Ld ≠ 0) :
    (psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2) =
      (psi_t * (psi_xx + psi_yy) + psi_xt * psi_x + psi_yt * psi_y) -
        psi_t * ((psi_xx + psi_yy) - psi / Ld ^ 2) := by
  ring

/-- Energy-density rate in conservation form: for a nonzero deformation
radius `Ld`, with
`e_t = psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld^2` the time
derivative of the energy density `0.5 * (|grad psi|^2 + psi^2 / Ld^2)`,
`div (psi * grad psi_t) = (psi_x * psi_xt + psi * psi_xxt) +
(psi_y * psi_yt + psi * psi_yyt)`, and
`q_t = (psi_xxt + psi_yyt) - psi_t / Ld^2` the time derivative of
`q = Delta psi - psi / Ld^2 + beta * y` (`beta * y` does not depend on
time), one has `e_t = div (psi * grad psi_t) - psi * q_t`. -/
theorem energy_density_rate_eq
    {psi psi_x psi_y psi_t psi_xt psi_yt psi_xxt psi_yyt Ld q_t : ℝ} (hLd : Ld ≠ 0)
    (hqt : q_t = (psi_xxt + psi_yyt) - psi_t / Ld ^ 2) :
    psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2 =
      ((psi_x * psi_xt + psi * psi_xxt) + (psi_y * psi_yt + psi * psi_yyt)) -
        psi * q_t := by
  rw [hqt]
  field_simp
  ring

/-- `psi * J(psi, q)` is a divergence: with `q_xy` the mixed partial of
`q`, the flux `(psi^2 / 2 * q_y, -psi^2 / 2 * q_x)` has divergence
`(psi * psi_x * q_y + psi^2 / 2 * q_xy) +
(-(psi * psi_y * q_x) - psi^2 / 2 * q_xy)`, which is
`psi * J(psi, q)`. -/
theorem psi_mul_jacobian_eq_div {psi psi_x psi_y q_x q_y q_xy : ℝ} :
    (psi * psi_x * q_y + psi ^ 2 / 2 * q_xy) +
      (-(psi * psi_y * q_x) - psi ^ 2 / 2 * q_xy) =
      psi * (psi_x * q_y - psi_y * q_x) := by
  ring

/-- **Energy conservation identity.** For a nonzero deformation radius
`Ld`, with `e_t` and `q_t = (psi_xxt + psi_yyt) - psi_t / Ld^2` as in
`energy_density_rate_eq`,
and the QG equation `q_t = -J(psi, q)`, the energy density satisfies
`e_t = div G` for
`G = (psi * psi_xt + psi^2 / 2 * q_y, psi * psi_yt - psi^2 / 2 * q_x)`,
whose divergence is written out on the right (`q_xy` is the mixed
partial of `q`). On the walls `psi = 0`, so `G_y = 0` there; with
`Lx`-periodic `x`, the channel integral of `div G` vanishes by the
divergence theorem, which is energy conservation. -/
theorem energy_flux_divergence_of_qg
    {psi psi_x psi_y psi_t psi_xt psi_yt psi_xxt psi_yyt Ld q_t q_x q_y q_xy : ℝ}
    (hLd : Ld ≠ 0) (hqt : q_t = (psi_xxt + psi_yyt) - psi_t / Ld ^ 2)
    (hqg : q_t = -(psi_x * q_y - psi_y * q_x)) :
    psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2 =
      ((psi_x * psi_xt + psi * psi_xxt) + (psi * psi_x * q_y + psi ^ 2 / 2 * q_xy)) +
        ((psi_y * psi_yt + psi * psi_yyt) +
          (-(psi * psi_y * q_x) - psi ^ 2 / 2 * q_xy)) := by
  rw [energy_density_rate_eq hLd hqt, hqg]
  ring

/-- Zero `x`-derivatives give a zero Jacobian: `psi_x = 0` and `q_x = 0`
give `J(psi, q) = psi_x * q_y - psi_y * q_x = 0`, so the QG advection
term vanishes for a flow with no `x` dependence. This is the generic
algebraic fact; no particular streamfunction is formalized here. -/
theorem jacobian_eq_zero_of_x_derivs_eq_zero {psi_x q_x psi_y q_y : ℝ} (hx : psi_x = 0)
    (hqx : q_x = 0) : psi_x * q_y - psi_y * q_x = 0 := by
  rw [hx, hqx]
  ring

end EarthScience
