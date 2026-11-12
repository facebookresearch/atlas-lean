/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.O01SeawaterStratification

/-!
# Seawater-stratification checks

Concrete consumers of `PhyslibExt.EarthScience.O01SeawaterStratification`:
the gradient of the linear profile at `rho0 = 1025, beta = 0.02`, the
`N^2` identity at `g = 9.81`, and the stable/neutral/unstable sign
classification.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At the
concrete parameters `rho_z = -0.02` and
`N^2 = -(9.81 / 1025) * (-0.02) = 9.81 * 0.02 / 1025 > 0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete gradient and `N^2`
- B. Stability signs and boundary cases

## iv. References

- `PhyslibExt.EarthScience.O01SeawaterStratification`
-/

/-- Public shape of the density-gradient theorem. -/
example {rho0 beta : ℝ} (z : ℝ) :
    HasDerivAt (fun z => rho0 - beta * z) (-beta) z :=
  EarthScience.boussinesq_density_deriv z

/-- Concrete gradient. -/
example (z : ℝ) :
    HasDerivAt (fun z => (1025 : ℝ) - 0.02 * z) (-(0.02 : ℝ)) z :=
  EarthScience.boussinesq_density_deriv z

/-- Concrete `N^2` identity. -/
example : -((9.81 : ℝ) / 1025) * (-(0.02 : ℝ)) = 9.81 * 0.02 / 1025 :=
  EarthScience.brunt_vaisala_from_gradient (show (1025 : ℝ) ≠ 0 by norm_num)

/-- Stable case: `beta > 0` gives `N^2 > 0`. -/
example : (0 < (9.81 : ℝ) * 0.02 / 1025 ↔ 0 < (0.02 : ℝ)) ∧
    ((9.81 : ℝ) * 0.02 / 1025 = 0 ↔ (0.02 : ℝ) = 0) ∧
      ((9.81 : ℝ) * 0.02 / 1025 < 0 ↔ (0.02 : ℝ) < 0) :=
  EarthScience.brunt_vaisala_sq_sign_ocean (by norm_num) (by norm_num)

/-- Uniform density (`beta = 0`) gives `N^2 = 0`. -/
example : (9.81 : ℝ) * (0 : ℝ) / 1025 = 0 := by
  have h := EarthScience.brunt_vaisala_sq_sign_ocean (g := 9.81) (beta := 0)
    (rho0 := 1025) (by norm_num) (by norm_num)
  exact (h.2.1).mpr rfl
