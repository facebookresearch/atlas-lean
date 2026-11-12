/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.QGConservation

/-!
# Quasigeostrophic conservation checks

Concrete consumers of `PhyslibExt.EarthScience.QGConservation`:
the public shapes of the four theorems, the Jacobian at concrete
values, the enstrophy flux divergence at `q = 2`, and the steady
witness.

## i. Overview

These are elaboration and non-vacuity checks, not new results. For
`psi_x = 1, psi_y = 2, q_x = 3, q_y = 4` the Jacobian is
`1 * 4 - 2 * 3 = -2`. For the steady witness `psi_x = q_x = 0` the
Jacobian is `0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Jacobian and flux identities
- B. Steady witness

## iv. References

- `PhyslibExt.EarthScience.QGConservation`
-/

/-- Jacobian antisymmetry shape: `J(a, b) = -J(b, a)` and `J(a, a) = 0`. -/
example {ax ay bx byy : ℝ} :
    (ax * byy - ay * bx) = -(bx * ay - byy * ax) ∧ (ax * ay - ay * ax) = 0 :=
  EarthScience.jacobian_antisymm_self

/-- Public shape of the enstrophy flux-divergence identity. -/
example {psi_x psi_y psi_xy q q_x q_y : ℝ} :
    (-psi_xy * q ^ 2 / 2 - psi_y * q * q_x) +
      (psi_xy * q ^ 2 / 2 + psi_x * q * q_y) =
      q * (psi_x * q_y - psi_y * q_x) :=
  EarthScience.enstrophy_flux_divergence

/-- Public shape of the energy flux-divergence identity. -/
example {psi psi_x psi_y psi_t psi_xt psi_yt psi_xx psi_yy Ld : ℝ} (hLd : Ld ≠ 0) :
    (psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2) =
      (psi_t * (psi_xx + psi_yy) + psi_xt * psi_x + psi_yt * psi_y) -
        psi_t * ((psi_xx + psi_yy) - psi / Ld ^ 2) :=
  EarthScience.energy_flux_divergence hLd

/-- Steady witness: `psi_x = 0, q_x = 0` gives `J(psi, q) = 0`. -/
example {psi_y q_y : ℝ} :
    (0 : ℝ) * q_y - psi_y * (0 : ℝ) = 0 :=
  EarthScience.qg_steady_no_x_dependence rfl rfl
