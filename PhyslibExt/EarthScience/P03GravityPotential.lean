/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Point-mass potential: gradient and radial acceleration

## i. Overview

For the stipulated point-mass potential `Φ(r) = -G * M / r` on `r > 0`,
`dΦ/dr = G * M / r ^ 2`, so the radial acceleration is `-G * M / r ^ 2`
(inward). `Φ` is a specific potential (`L ^ 2 / T ^ 2`); the singular
origin is excluded, and extended bodies would need a separately proved
spherical-enclosed-mass relation.

## ii. Key results

- `EarthScience.hasDerivAt_pointMass_potential`: `dΦ/dr = G * M / r ^ 2`.
- `EarthScience.pointMass_radial_acceleration`: the radial acceleration is
  `-G * M / r ^ 2`.

## iii. Table of contents

- A. Potential gradient
- B. Radial acceleration

## iv. References

- `hasDerivAt_inv` / `HasDerivAt.const_mul` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- For the stipulated point-mass potential `Φ(r) = -G * M / r`,
`dΦ/dr = G * M / r ^ 2` on `r > 0`. -/
theorem hasDerivAt_pointMass_potential {G M : ℝ} {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => -G * M / r) (G * M / r ^ 2) r := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have h := (hasDerivAt_inv hr').const_mul (-G * M)
  have heq : (fun r => -G * M / r) = (fun y => (-G * M) * y⁻¹) := by
    funext y
    rw [div_eq_mul_inv]
  rw [heq]
  convert h using 1
  field_simp

/-- The radial acceleration is the negative potential gradient:
`-dΦ/dr = -G * M / r ^ 2`. -/
theorem pointMass_radial_acceleration {G M : ℝ} {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => -G * M / r) (G * M / r ^ 2) r ∧
      -(G * M / r ^ 2) = -G * M / r ^ 2 := by
  exact ⟨hasDerivAt_pointMass_potential hr, by ring⟩

end EarthScience
