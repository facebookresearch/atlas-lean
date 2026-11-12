/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.P17Geostrophic

/-!
# Geostrophic checks

Concrete consumers of `PhyslibExt.EarthScience.P17Geostrophic`:
the geostrophic formula at `f = 1e-4, rho0 = 1025, px = 0.01, py = -0.02`,
uniqueness, and the southern-hemisphere sign.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At the
concrete parameters `ux = 0.02 / (1025 * 1e-4)` and
`uy = 0.01 / (1025 * 1e-4)`; the f = 0 equator is excluded.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete geostrophic velocity
- B. Uniqueness and hemisphere sign

## iv. References

- `PhyslibExt.EarthScience.P17Geostrophic`
-/

/-- Public shape of the geostrophic-velocity theorem. -/
example {f rho0 px py ux uy : ℝ} (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hx : f * ux = -py / rho0) (hy : -f * uy = -px / rho0) :
    ux = -py / (rho0 * f) ∧ uy = px / (rho0 * f) :=
  EarthScience.geostrophic_velocity hf hrho hx hy

/-- Concrete geostrophic velocity: `f = 1e-4, rho0 = 1025, px = 0.01, py = -0.02`. -/
example : (1e-4 : ℝ) * (0.02 / (1025 * 1e-4)) = -(-0.02) / 1025 ∧
    -(1e-4 : ℝ) * (0.01 / (1025 * 1e-4)) = -(0.01) / 1025 := by
  constructor <;> field_simp

/-- Uniqueness shape. -/
example {f rho0 px py ux1 uy1 ux2 uy2 : ℝ} (hf : f ≠ 0) (hrho : rho0 ≠ 0)
    (hx1 : f * ux1 = -py / rho0) (hy1 : -f * uy1 = -px / rho0)
    (hx2 : f * ux2 = -py / rho0) (hy2 : -f * uy2 = -px / rho0) :
    ux1 = ux2 ∧ uy1 = uy2 :=
  EarthScience.geostrophic_velocity_unique hf hrho hx1 hy1 hx2 hy2

/-- Southern hemisphere: `f < 0, py > 0` gives `ux > 0`. -/
example {f rho0 px py ux uy : ℝ} (hf : f < 0) (hrho : 0 < rho0) (hpy : 0 < py)
    (hx : f * ux = -py / rho0) (hy : -f * uy = -px / rho0) :
    0 < ux :=
  EarthScience.geostrophic_velocity_southern hf hrho hpy hx hy
