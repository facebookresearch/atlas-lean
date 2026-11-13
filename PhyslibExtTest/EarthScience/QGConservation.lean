/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.QGConservation

/-!
# Quasigeostrophic conservation checks

Concrete consumers of `PhyslibExt.EarthScience.QGConservation`:
the public shapes of the theorems, a concrete instance of the QG
energy identity, and the zero-`x`-derivative Jacobian.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
energy identity's hypotheses hold at `psi = psi_x = q_y = psi_t = Ld = 1`
with every other partial `0`: then `J(psi, q) = 1` and
`q_t = 0 + 0 - 1 / 1 = -1 = -J(psi, q)`. With `psi_x = q_x = 0` the
Jacobian is `0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Jacobian and flux identities
- B. Energy conservation identity
- C. Zero `x`-derivatives

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

/-- Public shape of the `psi_t * grad psi` energy-density identity. -/
example {psi psi_x psi_y psi_t psi_xt psi_yt psi_xx psi_yy Ld : ℝ} (hLd : Ld ≠ 0) :
    (psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2) =
      (psi_t * (psi_xx + psi_yy) + psi_xt * psi_x + psi_yt * psi_y) -
        psi_t * ((psi_xx + psi_yy) - psi / Ld ^ 2) :=
  EarthScience.energy_flux_divergence hLd

/-- Public shape of `e_t = div (psi * grad psi_t) - psi * q_t`. -/
example {psi psi_x psi_y psi_t psi_xt psi_yt psi_xxt psi_yyt Ld q_t : ℝ}
    (hqt : q_t = (psi_xxt + psi_yyt) - psi_t / Ld ^ 2) :
    psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2 =
      ((psi_x * psi_xt + psi * psi_xxt) + (psi_y * psi_yt + psi * psi_yyt)) -
        psi * q_t :=
  EarthScience.energy_density_rate_eq hqt

/-- Public shape of `psi * J(psi, q) = div (psi^2 / 2 * q_y, -psi^2 / 2 * q_x)`. -/
example {psi psi_x psi_y q_x q_y q_xy : ℝ} :
    (psi * psi_x * q_y + psi ^ 2 / 2 * q_xy) +
      (-(psi * psi_y * q_x) - psi ^ 2 / 2 * q_xy) =
      psi * (psi_x * q_y - psi_y * q_x) :=
  EarthScience.psi_mul_jacobian_eq_div

/-- Public shape of the QG energy conservation identity `e_t = div G`. -/
example {psi psi_x psi_y psi_t psi_xt psi_yt psi_xxt psi_yyt Ld q_t q_x q_y q_xy : ℝ}
    (hqt : q_t = (psi_xxt + psi_yyt) - psi_t / Ld ^ 2)
    (hqg : q_t = -(psi_x * q_y - psi_y * q_x)) :
    psi_x * psi_xt + psi_y * psi_yt + psi * psi_t / Ld ^ 2 =
      ((psi_x * psi_xt + psi * psi_xxt) + (psi * psi_x * q_y + psi ^ 2 / 2 * q_xy)) +
        ((psi_y * psi_yt + psi * psi_yyt) +
          (-(psi * psi_y * q_x) - psi ^ 2 / 2 * q_xy)) :=
  EarthScience.energy_flux_divergence_of_qg hqt hqg

/-- Non-vacuity of the QG energy identity: `psi = psi_x = q_y = psi_t = Ld = 1`,
every other partial `0`, and `q_t = -1` satisfy both hypotheses. -/
example :
    (1 : ℝ) * 0 + 0 * 0 + 1 * 1 / 1 ^ 2 =
      ((1 * 0 + 1 * 0) + (1 * 1 * 1 + 1 ^ 2 / 2 * 0)) +
        ((0 * 0 + 1 * 0) + (-(1 * 0 * 0) - 1 ^ 2 / 2 * 0)) :=
  EarthScience.energy_flux_divergence_of_qg (psi := 1) (psi_x := 1) (psi_y := 0)
    (psi_t := 1) (psi_xt := 0) (psi_yt := 0) (psi_xxt := 0) (psi_yyt := 0) (Ld := 1)
    (q_t := -1) (q_x := 0) (q_y := 1) (q_xy := 0) (by norm_num) (by norm_num)

/-- Zero `x`-derivatives: `psi_x = 0, q_x = 0` gives `J(psi, q) = 0`. -/
example {psi_y q_y : ℝ} :
    (0 : ℝ) * q_y - psi_y * (0 : ℝ) = 0 :=
  EarthScience.jacobian_eq_zero_of_x_derivs_eq_zero rfl rfl
