/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.P02NewtonianEnergy

/-!
# Kinetic-energy checks

Concrete consumers of `PhyslibExt.EarthScience.P02NewtonianEnergy`: a
one-dimensional particle with `m = 2`, `v t = 3 * t`, `a = 3`, the
stationary-particle boundary, and nonnegativity at zero mass.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At `t = 1`
the example has `K = 9` and `K' = inner (2 • 3) 3 = 18`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. One-dimensional particle
- B. Stationary and zero-mass boundaries

## iv. References

- `PhyslibExt.EarthScience.P02NewtonianEnergy`
-/

/-- Public shape of the kinetic-energy derivative theorem. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℝ} {v : ℝ → E} {a : ℝ → E} {t : ℝ}
    (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun t => m * ‖v t‖ ^ 2 / 2) (inner ℝ (m • a t) (v t)) t :=
  EarthScience.hasDerivAt_kinetic_energy hv

/-- One-dimensional particle `m = 2`, `v t = 3 * t`, `a = 3`. -/
example (t : ℝ) :
    HasDerivAt (fun t => (2 : ℝ) * ‖3 * t‖ ^ 2 / 2)
      (inner ℝ ((2 : ℝ) • (3 : ℝ)) (3 * t)) t := by
  have hv : HasDerivAt (fun t : ℝ => 3 * t) (3 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
  exact EarthScience.hasDerivAt_kinetic_energy (m := 2) (v := fun t : ℝ => 3 * t) (a := fun _ : ℝ => (3 : ℝ)) hv

/-- Stationary particle: velocity `0` gives kinetic energy `0`. -/
example : (0 : ℝ) * ‖(0 : ℝ)‖ ^ 2 / 2 = 0 := by norm_num

/-- Zero-mass boundary: kinetic energy is nonnegative (and zero) at `m = 0`. -/
example (v : ℝ) : 0 ≤ (0 : ℝ) * ‖v‖ ^ 2 / 2 :=
  EarthScience.kinetic_energy_nonneg (le_refl 0) v

/-- Nonnegativity with `m = 2` at a concrete velocity. -/
example : 0 ≤ (2 : ℝ) * ‖(5 : ℝ)‖ ^ 2 / 2 :=
  EarthScience.kinetic_energy_nonneg (by norm_num) 5
