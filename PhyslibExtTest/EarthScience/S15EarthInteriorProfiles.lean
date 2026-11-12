/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.S15EarthInteriorProfiles

/-!
# Earth-interior profile checks

Concrete consumers of `PhyslibExt.EarthScience.S15EarthInteriorProfiles`:
`ρ = 5000, g = 10, φ = 10^8` gives `dρ / dr = -1 / 2000`, and the
uniform-density shell derivative at `ρ = 3000`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric density gradient
- B. Shell derivative

## iv. References

- `PhyslibExt.EarthScience.S15EarthInteriorProfiles`
-/

/-- Numeric density gradient: `ρ = 5000, g = 10, φ = 10^8` gives `dρ / dr = -1 / 2000`. -/
example : (-1 / 2000 : ℝ) = -5000 * 10 / 100000000 :=
  EarthScience.density_gradient_adams_williamson (ρ := 5000) (g := 10)
    (φ := 100000000) (dp := -50000) (drho := -1 / 2000)
    (by norm_num) (by norm_num) (by norm_num)

/-- The numeric gradient is negative. -/
example : (-1 / 2000 : ℝ) < 0 :=
  EarthScience.density_gradient_negative (ρ := 5000) (g := 10) (φ := 100000000)
    (drho := -1 / 2000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Uniform-density shell derivative at `ρ = 3000`. -/
example (r : ℝ) :
    HasDerivAt (fun r => (4 / 3 : ℝ) * Real.pi * r ^ 3 * 3000)
      (4 * Real.pi * r ^ 2 * 3000) r :=
  EarthScience.hasDerivAt_enclosed_mass_uniform (ρ := 3000) (r := r)
