/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Graduate quasigeostrophic conservation

For quasigeostrophic potential vorticity
`q = Delta psi - psi / Ld^2 + beta * y` with `q_t + J(psi, q) = 0`,
energy `E = 0.5 * integral (|grad psi|^2 + psi^2 / Ld^2)` and
enstrophy `0.5 * integral q^2` are conserved in the channel with
`Lx`-periodic `x` and `psi = 0` walls. This module proves the
divergence-form identities that carry the conservation: the
enstrophy flux divergence is `q * J(psi, q)`, and the energy-density
time derivative is a flux divergence minus `psi_t * q` plus
`beta * y * psi_t` (with `q = Delta psi - psi / Ld^2 + beta * y`).
Integrated over the channel, the flux divergences are boundary terms
vanishing under the stated periodic / wall conditions; that
integration by the divergence theorem is documented here, not
formalized as a separate integral theorem. Conditional identities
only: no PDE existence is claimed.

## i. Overview

The Jacobian is antisymmetric with `J(a, a) = 0`. The enstrophy flux
`(-psi_y * q^2 / 2, psi_x * q^2 / 2)` has divergence `q * J(psi, q)`,
so `d/dt (q^2 / 2) = -q * J(psi, q)` is in divergence form. The
energy identity rewrites `e_t` as a flux divergence minus
`psi_t * (Delta psi - psi / Ld^2)`. The steady witness
`psi = sin(pi * y / Ly)` (no `x` dependence) has `J(psi, q) = 0`.

## ii. Key results

- `EarthScience.jacobian_antisymm_self`: Jacobian antisymmetry and diagonal.
- `EarthScience.enstrophy_flux_divergence`: enstrophy flux divergence.
- `EarthScience.energy_flux_divergence`: energy-density flux identity.
- `EarthScience.qg_steady_no_x_dependence`: steady witness has `J = 0`.

## iii. Table of contents

- A. Quasigeostrophic conservation identities

## iv. References

- `ring` in Mathlib (all four identities are polynomial identities).
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
/-- Energy flux divergence: with `e_t = psi_x * psi_xt + psi_y * psi_yt
+ psi * psi_t / Ld^2` the time derivative of the energy density
`0.5 * (|grad psi|^2 + psi^2 / Ld^2)`, and flux divergence
`psi_t * (psi_xx + psi_yy) + psi_xt * psi_x + psi_yt * psi_y`,
one has `e_t = div - psi_t * ((psi_xx + psi_yy) - psi / Ld^2)`.
Since `q = (psi_xx + psi_yy) - psi / Ld^2 + beta * y`, this is
`e_t = div - psi_t * q + beta * y * psi_t`; integrated, the divergence
term is a boundary term vanishing under the channel conditions. -/
theorem energy_flux_divergence {psi psi_x psi_y psi_t psi_xt psi_yt psi_xx psi_yy Ld : ℝ}
    (hLd : Ld ≠ 0) :
    (psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2) =
      (psi_t * (psi_xx + psi_yy) + psi_xt * psi_x + psi_yt * psi_y) -
        psi_t * ((psi_xx + psi_yy) - psi / Ld ^ 2) := by
  ring

/-- Steady witness `psi = sin(pi * y / Ly)` (no `x` dependence):
`psi_x = 0` and `q_x = 0` give `J(psi, q) = 0`, so the QG advection
term vanishes and the steady state is consistent with `q_t = 0`. -/
theorem qg_steady_no_x_dependence {psi_x q_x psi_y q_y : ℝ} (hx : psi_x = 0)
    (hqx : q_x = 0) : psi_x * q_y - psi_y * q_x = 0 := by
  rw [hx, hqx]
  ring

end EarthScience
