/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.UpwindScheme

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Periodic face-flux advection step as the canonical upwind update

The conservative finite-volume step for constant-speed scalar advection on a uniform periodic
grid, written with physical face fluxes and cell masses, is the canonical periodic upwind
update.

## i. Overview

The model is scalar transport `∂ₜc + ∂ₓ(v c) = 0` with constant speed `v` in a periodic tube of
cross-section `area > 0`, cut into `n` cells of common length `dx > 0` indexed by `ZMod n`.
Cell `i` holds the mass `area * dx * c i`. Face `i` is the face between cell `i - 1` and cell
`i`, so cell `i` lies between its left face `i` and its right face `i + 1`; face fluxes are
positive toward increasing index. The physical upwind face flux is the cross-section times the
advective flux `v c` evaluated on the upstream side, `v⁺ c (i - 1) + v⁻ c i` with
`v⁺ = max v 0` and `v⁻ = min v 0`. One conservative step of length `dt` changes each cell mass
by inflow through the left face minus outflow through the right face, so every face flux enters
its two neighbouring cells with opposite signs.

For `v ≥ 0` this step is exactly the periodic upwind update
`c' i = (1 - ν) * c i + ν * c (i - 1)` with Courant number `ν = v * dt / dx`, the update of
`EarthScience.upwind_nonneg` and `EarthScience.upwind_sum_eq`. Reusing those results, the step
conserves the total mass `∑ i, area * dx * c i` for every `ν` and preserves nonnegativity when
`0 ≤ ν ≤ 1`. Above the CFL limit the total is still conserved but nonnegativity fails.

All quantities are exact real coordinates in one consistent unit system. Nonperiodic boundaries
and wells, moving meshes, reconstruction, consistency and convergence are not treated.

## ii. Key results

- `AdvectionError.isConservativeStep_upwindFaceFlux_iff`: the conservative shared-face step with
  the upwind face flux is the canonical upwind update with `ν = v * dt / dx`.
- `AdvectionError.upwindStep_mass_eq`: the step conserves the total mass for every `ν`.
- `AdvectionError.upwindStep_nonneg`: the step preserves nonnegativity when `ν ≤ 1`.

## iii. Table of contents

- A. Face flux and the conservative step
- B. Identification with the upwind update
- C. Conservation and positivity

## iv. References

- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press
  (2002), Chapter 4: conservative finite-volume updates, the upwind flux for advection and the
  CFL condition.
- `EarthScience.upwind_nonneg` and `EarthScience.upwind_sum_eq`
  (`PhyslibExt.EarthScience.UpwindScheme`).
-/

@[expose] public section

namespace AdvectionError

/-! ## A. Face flux and the conservative step -/

/-- Upwind face flux through face `i`, the face between cell `i - 1` and cell `i`, positive
toward increasing index: the cross-section `area` times the advective flux `v c` taken on the
upstream side, `max v 0 * c (i - 1) + min v 0 * c i`. -/
noncomputable def upwindFaceFlux {n : ℕ} (area v : ℝ) (c : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  area * (max v 0 * c (i - 1) + min v 0 * c i)

/-- Conservative shared-face step in mass form on `n` periodic cells of length `dx` and
cross-section `area`: over the time step `dt` the mass `area * dx * c i` of cell `i` gains the
inflow `dt * F i` through its left face `i` and loses the outflow `dt * F (i + 1)` through its
right face `i + 1`. -/
def IsConservativeStep {n : ℕ} (area dx dt : ℝ) (F c cNext : ZMod n → ℝ) : Prop :=
  ∀ i, area * dx * cNext i = area * dx * c i + dt * (F i - F (i + 1))

/-- For a nonnegative speed the upwind face flux carries the upstream cell value. -/
lemma upwindFaceFlux_of_nonneg {n : ℕ} {area v : ℝ} (hv : 0 ≤ v) (c : ZMod n → ℝ)
    (i : ZMod n) :
    upwindFaceFlux area v c i = area * v * c (i - 1) := by
  unfold upwindFaceFlux
  rw [max_eq_left hv, min_eq_right hv]
  ring

/-! ## B. Identification with the upwind update -/

/-- For positive `area` and `dx` and speed `v ≥ 0`, the state `cNext` is reached from `c` by the
conservative shared-face step with the upwind face flux exactly when it is the canonical
periodic upwind update with Courant number `ν = v * dt / dx`. -/
lemma isConservativeStep_upwindFaceFlux_iff {n : ℕ} {area dx dt v : ℝ} (harea : 0 < area)
    (hdx : 0 < dx) (hv : 0 ≤ v) (c cNext : ZMod n → ℝ) :
    IsConservativeStep area dx dt (upwindFaceFlux area v c) c cNext ↔
      ∀ i, cNext i = (1 - v * dt / dx) * c i + v * dt / dx * c (i - 1) := by
  have hADX : area * dx ≠ 0 := mul_ne_zero (ne_of_gt harea) (ne_of_gt hdx)
  have hdxne : dx ≠ 0 := ne_of_gt hdx
  unfold IsConservativeStep
  constructor
  · intro h i
    have hi := h i
    simp only [upwindFaceFlux_of_nonneg hv] at hi
    rw [add_sub_cancel_right] at hi
    have hid : area * dx * ((1 - v * dt / dx) * c i + v * dt / dx * c (i - 1)) =
        area * dx * c i + dt * (area * v * c (i - 1) - area * v * c i) := by
      field_simp
      ring
    have h2 : area * dx * cNext i =
        area * dx * ((1 - v * dt / dx) * c i + v * dt / dx * c (i - 1)) := by
      rw [hi, hid]
    exact (mul_right_inj' hADX).mp h2
  · intro h i
    have hi := h i
    simp only [upwindFaceFlux_of_nonneg hv]
    rw [add_sub_cancel_right]
    have hid : area * dx * ((1 - v * dt / dx) * c i + v * dt / dx * c (i - 1)) =
        area * dx * c i + dt * (area * v * c (i - 1) - area * v * c i) := by
      field_simp
      ring
    rw [hi, hid]

/-! ## C. Conservation and positivity -/

/-- Conservation for every Courant number: the conservative upwind step preserves the total
mass `∑ i, area * dx * c i`. -/
lemma upwindStep_mass_eq {n : ℕ} [NeZero n] {area dx dt v : ℝ} (harea : 0 < area)
    (hdx : 0 < dx) (hv : 0 ≤ v) {c cNext : ZMod n → ℝ}
    (hstep : IsConservativeStep area dx dt (upwindFaceFlux area v c) c cNext) :
    ∑ i, area * dx * cNext i = ∑ i, area * dx * c i := by
  have hup := (isConservativeStep_upwindFaceFlux_iff harea hdx hv c cNext).mp hstep
  have hcongr : (∑ i, area * dx * cNext i) =
      ∑ i, area * dx * ((1 - v * dt / dx) * c i + v * dt / dx * c (i - 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hup i]
  rw [hcongr, ← Finset.mul_sum, ← Finset.mul_sum, EarthScience.upwind_sum_eq]

/-- Positivity under the CFL condition: for `dt ≥ 0`, `v ≥ 0` and `v * dt / dx ≤ 1`, the
conservative upwind step maps nonnegative cell values to nonnegative cell values. -/
lemma upwindStep_nonneg {n : ℕ} [NeZero n] {area dx dt v : ℝ} (harea : 0 < area)
    (hdx : 0 < dx) (hdt : 0 ≤ dt) (hv : 0 ≤ v) (hcfl : v * dt / dx ≤ 1)
    {c cNext : ZMod n → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hstep : IsConservativeStep area dx dt (upwindFaceFlux area v c) c cNext) :
    ∀ i, 0 ≤ cNext i := by
  have hup := (isConservativeStep_upwindFaceFlux_iff harea hdx hv c cNext).mp hstep
  have hν0 : 0 ≤ v * dt / dx := div_nonneg (mul_nonneg hv hdt) (le_of_lt hdx)
  have h := EarthScience.upwind_nonneg (v * dt / dx) hν0 hcfl c hc
  intro i
  rw [hup i]
  exact h i

end AdvectionError
