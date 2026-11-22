/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# Hydrostatic columns

A hydrostatic column of constant density `rho` under constant gravity of
magnitude `g`, with pressure `p0` at the free surface `z = 0`, has pressure
profile `p(z) = p0 - rho * g * z` in height coordinates (`z` upward),
satisfying `dp/dz = -rho * g` and `p(0) = p0`. In depth coordinates `d = -z`
(downward) the same column reads `p(d) = p0 + rho * g * d`, with
`dp/dd = rho * g`.

## i. Overview

`hydrostatic_pressure` and `hydrostatic_pressure_depth` are signed
identities: they hold for all real `p0`, `rho`, `g` and coordinates, so they
also accept negative density or gravity, and points above the free surface
where the affine profile becomes negative. Each pairs the derivative of an
affine function with an evaluation: the surface value `p(0) = p0` in height
coordinates, and agreement with the height profile at `d = -z` in depth
coordinates.

The physical regime is `p0 > 0`, `rho > 0`, `g > 0`, at points in the fluid
below the free surface (`d ≥ 0`). There `hydrostatic_pressure_physical` shows
that the pressure strictly increases with depth and is at least the surface
pressure, hence positive.

Hydrostatic balance is stipulated; the results show that the profile is
a solution of `dp/dz = -rho * g` with `p(0) = p0` (uniqueness is not
proved here), not a derivation of the balance law itself.

## ii. Key results

- `EarthScience.hydrostatic_pressure`: height-coordinate profile,
  derivative and surface value (signed identity).
- `EarthScience.hydrostatic_pressure_depth`: depth-coordinate profile,
  derivative and agreement with the height form (signed identity).
- `EarthScience.hydrostatic_pressure_physical`: for `p0, rho, g > 0`, the
  pressure strictly increases with depth and, below the free surface, is at
  least `p0`, hence positive.

## iii. Table of contents

- A. Height coordinates
- B. Depth coordinates
- C. Physical regime

## iv. References

- L. D. Landau and E. M. Lifshitz, *Fluid Mechanics*, 2nd ed., Pergamon
  Press, 1987, §3 (Hydrostatics), equation (3.2): a fluid of constant density
  at rest in a uniform gravitational field, with the `z`-axis vertically
  upward and a free surface at height `h` under external pressure `p0`, has
  `p = p0 + rho * g * (h - z)`. Here the free surface is at `h = 0`, so
  `p(z) = p0 - rho * g * z`, and the depth below it is `d = h - z = -z`.
- `HasDerivAt` API in `Mathlib/Analysis/Calculus/Deriv/Add.lean`.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Height coordinates -/

/-- Hydrostatic column, as a signed identity: `p(z) = p0 - ρ * g * z` satisfies
`dp/dz = -ρ * g` and `p(0) = p0` for all real `p0`, `ρ`, `g`, `z`. For the physical
regime see `hydrostatic_pressure_physical`. -/
theorem hydrostatic_pressure (p0 ρ g : ℝ) (z : ℝ) :
    HasDerivAt (fun z => p0 - ρ * g * z) (-(ρ * g)) z ∧
      (fun z => p0 - ρ * g * z) 0 = p0 := by
  constructor
  · have h1 : HasDerivAt (fun z : ℝ => ρ * g * z) (ρ * g) z := by
      have h := (hasDerivAt_id' z).const_mul (ρ * g)
      simpa only [mul_one] using h
    have h2 : HasDerivAt (fun z : ℝ => p0 - ρ * g * z) (0 - ρ * g) z :=
      (hasDerivAt_const z p0).sub h1
    simpa only [zero_sub] using h2
  · simp

/-! ## B. Depth coordinates -/

/-- In depth coordinates `d = -z`, the same column reads
`p(d) = p0 + ρ * g * d`, with `dp/dd = ρ * g`. Signed identity: all real inputs. -/
theorem hydrostatic_pressure_depth (p0 ρ g : ℝ) (d : ℝ) :
    HasDerivAt (fun d => p0 + ρ * g * d) (ρ * g) d ∧
      (fun d => p0 + ρ * g * d) d = p0 - ρ * g * (-d) := by
  constructor
  · have h1 : HasDerivAt (fun d : ℝ => ρ * g * d) (ρ * g) d := by
      have h := (hasDerivAt_id' d).const_mul (ρ * g)
      simpa only [mul_one] using h
    have h2 : HasDerivAt (fun d : ℝ => p0 + ρ * g * d) (0 + ρ * g) d :=
      (hasDerivAt_const d p0).add h1
    simpa only [zero_add] using h2
  · ring

/-! ## C. Physical regime -/

/-- Hydrostatic column in the physical regime: for surface pressure `p0 > 0`, density
`ρ > 0` and gravity magnitude `g > 0`, the depth profile `p(d) = p0 + ρ * g * d`
strictly increases with depth, and at every depth `d ≥ 0` below the free surface the
pressure is at least the surface pressure `p0`, hence positive. -/
theorem hydrostatic_pressure_physical {p0 ρ g : ℝ} (hp0 : 0 < p0) (hρ : 0 < ρ)
    (hg : 0 < g) :
    StrictMono (fun d : ℝ => p0 + ρ * g * d) ∧
      ∀ d : ℝ, 0 ≤ d → p0 ≤ p0 + ρ * g * d ∧ 0 < p0 + ρ * g * d := by
  have hρg : 0 < ρ * g := mul_pos hρ hg
  refine ⟨fun a b hab => ?_, fun d hd => ?_⟩
  · exact (add_lt_add_iff_left p0).mpr (mul_lt_mul_of_pos_left hab hρg)
  · have h : p0 ≤ p0 + ρ * g * d := le_add_of_nonneg_right (mul_nonneg hρg.le hd)
    exact ⟨h, hp0.trans_le h⟩

end EarthScience
