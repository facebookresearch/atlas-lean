/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.StaticStability

/-!
# Static-stability checks

Concrete consumers of `PhyslibExt.EarthScience.StaticStability`:
the buoyancy formula at `g = 9.81, a = 0.003, theta0 = 300, zeta = 10`,
the stable/neutral/unstable sign classification, and the oscillator form.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At the
concrete parameters the buoyancy acceleration is
`-(9.81 * 0.003 / 300) * 10`, and `N^2 = 9.81 * 0.003 / 300 > 0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete buoyancy and stability signs
- B. Oscillator and boundary cases

## iv. References

- `PhyslibExt.EarthScience.StaticStability`
-/

/-- Public shape of the buoyancy-acceleration theorem. -/
example {g a theta0 zeta : ℝ} (hth : theta0 ≠ 0) :
    g * (theta0 - (theta0 + a * zeta)) / theta0 = -(g * a / theta0) * zeta :=
  EarthScience.potential_temp_buoyancy_accel hth

/-- Concrete buoyancy: admissible nonzero parameters. -/
example : (9.81 : ℝ) * (300 - (300 + 0.003 * 10)) / 300
    = -(9.81 * 0.003 / 300) * 10 :=
  EarthScience.potential_temp_buoyancy_accel (show (300 : ℝ) ≠ 0 by norm_num)

/-- Stable case: `a > 0` gives `N^2 > 0`. -/
example : (0 < (9.81 : ℝ) * 0.003 / 300 ↔ 0 < (0.003 : ℝ)) ∧
    ((9.81 : ℝ) * 0.003 / 300 = 0 ↔ (0.003 : ℝ) = 0) ∧
      ((9.81 : ℝ) * 0.003 / 300 < 0 ↔ (0.003 : ℝ) < 0) :=
  EarthScience.brunt_vaisala_sq_sign (by norm_num) (by norm_num)

/-- Neutral profile (`a = 0`) gives `N^2 = 0`. -/
example : (9.81 : ℝ) * (0 : ℝ) / 300 = 0 := by
  have h := EarthScience.brunt_vaisala_sq_sign (g := 9.81) (a := 0)
    (theta0 := 300) (by norm_num) (by norm_num)
  exact (h.2.1).mpr rfl

/-- Oscillator form for a parcel whose velocity obeys the buoyancy law. -/
example {zeta v : ℝ → ℝ} {t : ℝ} {g a theta0 : ℝ} (hth : theta0 ≠ 0)
    (hbuoy : HasDerivAt v (g * (theta0 - (theta0 + a * zeta t)) / theta0) t) :
    HasDerivAt v (-(g * a / theta0) * zeta t) t :=
  EarthScience.static_stability_oscillator hth hbuoy
