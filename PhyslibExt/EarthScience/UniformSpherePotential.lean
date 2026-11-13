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
public import Mathlib.Analysis.Calculus.Deriv.Inv

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform-sphere potential matches at its surface

## i. Overview

For a uniform sphere of radius `R`, the interior potential
`-G * M / (2 * R) * (3 - (r / R) ^ 2)` and the exterior potential
`-G * M / r` agree at the surface `r = R`: both equal `-G * M / R`,
and both have derivative `G * M / R ^ 2` there. Value and field
therefore match continuously across the surface. This is the explicit
closed-form interior/exterior solution for the uniform-density case;
no claim is made about non-uniform density profiles.

## ii. Key results

- `EarthScience.uniform_sphere_potential_matches_at_surface`: value
  and derivative match at `r = R`.

## iii. Table of contents

- A. Surface matching

## iv. References

- `HasDerivAt.const_mul`, `HasDerivAt.sub`, `HasDerivAt.mul` in Mathlib.
- `hasDerivAt_inv`, `hasDerivAt_const`, `hasDerivAt_id` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Surface matching -/

/-- An explicit uniform-sphere solution matches at its surface `r = R`:
the interior potential `-G*M/(2*R) * (3 - (r/R)^2)` equals `-G*M/R` at
`r = R`, its derivative there is `G*M/R^2`, and the exterior potential
`-G*M/r` has the same value and the same derivative at `r = R`, so value
and field match continuously across the surface. -/
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
  · have hinv : HasDerivAt (fun r : ℝ => r⁻¹) (-(R ^ 2)⁻¹) R := hasDerivAt_inv hRne
    have h : HasDerivAt (fun r : ℝ => (-G * M) * r⁻¹) ((-G * M) * (-(R ^ 2)⁻¹)) R :=
      hinv.const_mul (-G * M)
    have hfun : (fun r : ℝ => -G * M / r) = (fun r : ℝ => (-G * M) * r⁻¹) := by
      ext r
      rw [div_eq_mul_inv]
    have hval3 : (-G * M) * (-(R ^ 2)⁻¹) = G * M / R ^ 2 := by
      field_simp
    rw [hval3] at h
    rwa [hfun]

end EarthScience
