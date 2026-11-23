/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

import PhyslibExt.EarthScience.GravityPotential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform-sphere potential matches at its surface

## i. Overview

For a uniform sphere of mass `M` and radius `R`, the interior potential
`-G * M / (2 * R) * (3 - (r / R) ^ 2)` and the exterior potential
`-G * M / r` agree at the surface `r = R`: both equal `-G * M / R`,
and both have radial derivative `G * M / R ^ 2` there. Only these
pointwise facts at `r = R` are proved. The piecewise potential that
joins the two formulas is not defined here, and no continuity or
differentiability of such a joined function is claimed.

Both formulas are stipulated, not derived from Poisson's equation or
Newton's theorems. They are the closed-form potential of a homogeneous
sphere of density `ρ` and radius `R` (Binney and Tremaine, below):
`-2 * π * G * ρ * (R ^ 2 - r ^ 2 / 3)` for `r ≤ R` and `-G * M / r`
for `r ≥ R`, where `M = 4 * π * ρ * R ^ 3 / 3`. Substituting this `M`
turns the interior formula into the form used here. No claim is made
about non-uniform density profiles. The exterior derivative is the
point-mass result `EarthScience.hasDerivAt_pointMass_potential` at
`r = R`.

## ii. Key results

- `EarthScience.uniform_sphere_potential_matches_at_surface`: value
  and derivative match at `r = R`.

## iii. Table of contents

- A. Surface matching

## iv. References

- J. Binney and S. Tremaine, *Galactic Dynamics*, 2nd ed., Princeton
  University Press, 2008, Chapter 2 (Potential Theory), §2.2 (Spherical
  systems), "Potentials of some simple systems: homogeneous sphere":
  the interior and exterior potential of a homogeneous sphere.
- `EarthScience.hasDerivAt_pointMass_potential` in
  `PhyslibExt.EarthScience.GravityPotential`.
- `HasDerivAt.const_mul`, `HasDerivAt.sub`, `HasDerivAt.mul` in Mathlib.
- `hasDerivAt_const`, `hasDerivAt_id` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Surface matching -/

/-- The stipulated uniform-sphere potentials agree at the surface `r = R`:
the interior potential `-G*M/(2*R) * (3 - (r/R)^2)` equals `-G*M/R`, the
value of the exterior potential `-G*M/r` at `r = R`, and both have
derivative `G*M/R^2` at `r = R`. This is a statement at the single point
`r = R`; no joined piecewise potential is defined. -/
theorem uniform_sphere_potential_matches_at_surface
    {G M R : ℝ} (hR : 0 < R) :
    (fun r => -G * M / (2 * R) * (3 - (r / R) ^ 2)) R = -G * M / R ∧
    HasDerivAt (fun r => -G * M / (2 * R) * (3 - (r / R) ^ 2)) (G * M / R ^ 2) R ∧
    HasDerivAt (fun r => -G * M / r) (G * M / R ^ 2) R := by
  have hRne : R ≠ 0 := ne_of_gt hR
  refine ⟨?_, ?_, ?_⟩
  · have hvalue : -G * M / (2 * R) * (3 - (R / R) ^ 2) = -G * M / R := by
      field_simp
      ring
    exact hvalue
  · have h1 : HasDerivAt (fun r : ℝ => r / R) (1 / R) R := (hasDerivAt_id R).div_const R
    have hmul : HasDerivAt (fun r : ℝ => r / R * (r / R)) (1 / R * (R / R) + R / R * (1 / R)) R :=
      h1.mul h1
    have hsq : (fun r : ℝ => (r / R) ^ 2) = (fun r : ℝ => r / R * (r / R)) := by
      ext r
      rw [pow_two]
    have h2 : HasDerivAt (fun r : ℝ => (r / R) ^ 2) (1 / R * (R / R) + R / R * (1 / R)) R := by
      rw [hsq]
      exact hmul
    have h3 : HasDerivAt (fun r : ℝ => 3 - (r / R) ^ 2)
        (0 - (1 / R * (R / R) + R / R * (1 / R))) R :=
      (hasDerivAt_const R 3).sub h2
    have h4 : HasDerivAt (fun r : ℝ => -G * M / (2 * R) * (3 - (r / R) ^ 2))
        (-G * M / (2 * R) * (0 - (1 / R * (R / R) + R / R * (1 / R)))) R :=
      h3.const_mul _
    have hval : -G * M / (2 * R) * (0 - (1 / R * (R / R) + R / R * (1 / R))) = G * M / R ^ 2 := by
      field_simp
      ring
    rw [hval] at h4
    exact h4
  · exact hasDerivAt_pointMass_potential hR

end EarthScience
