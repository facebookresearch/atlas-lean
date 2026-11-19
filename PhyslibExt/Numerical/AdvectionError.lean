/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.UpwindScheme
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Periodic face-flux advection: the upwind update and a smooth traveling wave

The conservative finite-volume step for constant-speed scalar advection on a uniform periodic
grid, written with physical face fluxes and cell masses, is the canonical periodic upwind
update. A smooth traveling sine wave solves the continuous advection equation, with explicit
positivity and second-derivative bounds.

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

Parts D-G treat the traveling wave `c(t, x) = c₀ + a sin(2π (x - v t) / L)` of the continuous
equation `∂ₜc + v ∂ₓc = 0` on the real line, with mean `c₀`, amplitude `a`, speed `v` and spatial
period `L`. Every derivative is obtained by composing `Real.hasDerivAt_sin` and
`Real.hasDerivAt_cos` with the affine phase `θ = 2π (x - v t) / L`, not assumed. The spatial
derivative is `a (2π / L) cos θ` and the time derivative is `-v` times it, so the advection
equation holds at every point; the wave is jointly `C²` and, for `L ≠ 0`, has period `L` in `x`.
The second derivatives, `-a (2π / L)² sin θ` in space and `v²` times it in time, give the uniform
bounds `|∂ₓₓc| ≤ M` and `|∂ₜₜc| ≤ v² M` with `M = |a| (2π / L)²`. The wave is bounded below by
`c₀ - |a|`, hence positive when `|a| < c₀`; when `c₀ ≤ |a|` and `L ≠ 0` it takes a nonpositive
value at every time, so strict positivity needs the strict inequality.

All quantities are exact real coordinates in one consistent unit system. Nonperiodic boundaries
and wells, moving meshes, reconstruction, consistency and convergence are not treated.

## ii. Key results

- `AdvectionError.isConservativeStep_upwindFaceFlux_iff`: the conservative shared-face step with
  the upwind face flux is the canonical upwind update with `ν = v * dt / dx`.
- `AdvectionError.upwindStep_mass_eq`: the step conserves the total mass for every `ν`.
- `AdvectionError.upwindStep_nonneg`: the step preserves nonnegativity when `ν ≤ 1`.
- `AdvectionError.travelingWave_hasDerivAt_space`, `AdvectionError.travelingWave_hasDerivAt_time`:
  first derivatives of the traveling wave through the affine phase.
- `AdvectionError.travelingWave_advection`: the traveling wave satisfies `∂ₜc + v ∂ₓc = 0`.
- `AdvectionError.travelingWave_periodic`: spatial period `L` for `L ≠ 0`.
- `AdvectionError.travelingWave_pos`: positivity under `|a| < c₀`.
- `AdvectionError.travelingWave_space_bound`, `AdvectionError.travelingWave_time_bound`: the
  second-derivative bounds `M` and `v² M`.
- `AdvectionError.travelingWave_exists_nonpos`: no strict positivity when `c₀ ≤ |a|` and
  `L ≠ 0`.

## iii. Table of contents

- A. Face flux and the conservative step
- B. Identification with the upwind update
- C. Conservation and positivity
- D. The traveling wave and its derivatives
- E. Advection, periodicity and positivity
- F. Second-derivative bounds
- G. Failure of strict positivity

## iv. References

- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press
  (2002), Chapter 2: the advection equation and its traveling-wave solutions; Chapter 4:
  conservative finite-volume updates, the upwind flux for advection and the CFL condition.
- `EarthScience.upwind_nonneg` and `EarthScience.upwind_sum_eq`
  (`PhyslibExt.EarthScience.UpwindScheme`).
- Mathlib's `Real.hasDerivAt_sin` and `Real.hasDerivAt_cos`.
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

/-! ## D. The traveling wave and its derivatives -/

/-- The traveling sine wave `c(t, x) = c₀ + a sin(2π (x - v t) / L)` with mean `c₀`, amplitude
`a`, speed `v` and spatial period `L`. -/
noncomputable def travelingWave (c₀ a v L t x : ℝ) : ℝ :=
  c₀ + a * Real.sin (2 * Real.pi * (x - v * t) / L)

/-- The traveling wave is jointly `C²` in `(t, x)`. -/
lemma travelingWave_contDiff (c₀ a v L : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (travelingWave c₀ a v L)) := by
  have hvt : ContDiff ℝ 2 (fun p : ℝ × ℝ => v * p.1) :=
    contDiff_const.mul contDiff_fst
  have hsub : ContDiff ℝ 2 (fun p : ℝ × ℝ => p.2 - v * p.1) :=
    contDiff_snd.sub hvt
  have hmul : ContDiff ℝ 2 (fun p : ℝ × ℝ => 2 * Real.pi * (p.2 - v * p.1)) :=
    contDiff_const.mul hsub
  have hdiv : ContDiff ℝ 2 (fun p : ℝ × ℝ => 2 * Real.pi * (p.2 - v * p.1) / L) :=
    hmul.div_const L
  have hsin : ContDiff ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * Real.pi * (p.2 - v * p.1) / L)) :=
    hdiv.sin
  have hamul : ContDiff ℝ 2 (fun p : ℝ × ℝ => a * Real.sin (2 * Real.pi * (p.2 - v * p.1) / L)) :=
    contDiff_const.mul hsin
  have hadd : ContDiff ℝ 2
      (fun p : ℝ × ℝ => c₀ + a * Real.sin (2 * Real.pi * (p.2 - v * p.1) / L)) :=
    contDiff_const.add hamul
  have heq : Function.uncurry (travelingWave c₀ a v L) =
      (fun p : ℝ × ℝ => c₀ + a * Real.sin (2 * Real.pi * (p.2 - v * p.1) / L)) := by
    rfl
  rw [heq]
  exact hadd

/-- Spatial derivative through the affine phase: `∂ₓc = a (2π / L) cos θ`. -/
lemma travelingWave_hasDerivAt_space (c₀ a v L t x : ℝ) :
    HasDerivAt (fun y => travelingWave c₀ a v L t y)
      (a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (x - v * t) / L)) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - v * t) 1 x := (hasDerivAt_id x).sub_const (v * t)
  have h2 : HasDerivAt (fun y : ℝ => 2 * Real.pi * (y - v * t)) ((2 * Real.pi) * 1) x :=
    HasDerivAt.const_mul (2 * Real.pi) h1
  have hphase : HasDerivAt (fun y : ℝ => 2 * Real.pi * (y - v * t) / L) (2 * Real.pi / L) x := by
    have h3 := h2.div_const L
    simpa using h3
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * (y - v * t) / L))
      (Real.cos (2 * Real.pi * (x - v * t) / L) * (2 * Real.pi / L)) x := by
    have h := (Real.hasDerivAt_sin (2 * Real.pi * (x - v * t) / L)).comp x hphase
    simpa only [Function.comp_def] using h
  have hmul : HasDerivAt (fun y : ℝ => a * Real.sin (2 * Real.pi * (y - v * t) / L))
      (a * (Real.cos (2 * Real.pi * (x - v * t) / L) * (2 * Real.pi / L))) x :=
    HasDerivAt.const_mul a hsin
  have hadd : HasDerivAt (fun y : ℝ => c₀ + a * Real.sin (2 * Real.pi * (y - v * t) / L))
      (a * (Real.cos (2 * Real.pi * (x - v * t) / L) * (2 * Real.pi / L))) x :=
    HasDerivAt.const_add c₀ hmul
  have heq : (fun y => travelingWave c₀ a v L t y) =
      (fun y : ℝ => c₀ + a * Real.sin (2 * Real.pi * (y - v * t) / L)) := by
    rfl
  rw [heq]
  convert hadd using 1
  ring

/-- Time derivative through the affine phase: `∂ₜc = -v a (2π / L) cos θ`. -/
lemma travelingWave_hasDerivAt_time (c₀ a v L t x : ℝ) :
    HasDerivAt (fun τ => travelingWave c₀ a v L τ x)
      (-(v * (a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (x - v * t) / L)))) t := by
  have hmul : HasDerivAt (fun τ : ℝ => v * τ) (v * 1) t :=
    HasDerivAt.const_mul v (hasDerivAt_id t)
  have hsub : HasDerivAt (fun τ : ℝ => x - v * τ) (-(v * 1)) t :=
    HasDerivAt.const_sub x hmul
  have h2 : HasDerivAt (fun τ : ℝ => 2 * Real.pi * (x - v * τ)) ((2 * Real.pi) * (-(v * 1))) t :=
    HasDerivAt.const_mul (2 * Real.pi) hsub
  have hphase : HasDerivAt (fun τ : ℝ => 2 * Real.pi * (x - v * τ) / L)
      (-(v * (2 * Real.pi / L))) t := by
    have h3 := h2.div_const L
    convert h3 using 1
    ring
  have hsin : HasDerivAt (fun τ : ℝ => Real.sin (2 * Real.pi * (x - v * τ) / L))
      (Real.cos (2 * Real.pi * (x - v * t) / L) * (-(v * (2 * Real.pi / L)))) t := by
    have h := (Real.hasDerivAt_sin (2 * Real.pi * (x - v * t) / L)).comp t hphase
    simpa only [Function.comp_def] using h
  have hmul2 : HasDerivAt (fun τ : ℝ => a * Real.sin (2 * Real.pi * (x - v * τ) / L))
      (a * (Real.cos (2 * Real.pi * (x - v * t) / L) * (-(v * (2 * Real.pi / L))))) t :=
    HasDerivAt.const_mul a hsin
  have hadd : HasDerivAt (fun τ : ℝ => c₀ + a * Real.sin (2 * Real.pi * (x - v * τ) / L))
      (a * (Real.cos (2 * Real.pi * (x - v * t) / L) * (-(v * (2 * Real.pi / L))))) t :=
    HasDerivAt.const_add c₀ hmul2
  have heq : (fun τ => travelingWave c₀ a v L τ x) =
      (fun τ : ℝ => c₀ + a * Real.sin (2 * Real.pi * (x - v * τ) / L)) := by
    rfl
  rw [heq]
  convert hadd using 1
  ring

/-- Second spatial derivative: the spatial derivative of `c` has derivative
`-a (2π / L)² sin θ`. -/
lemma travelingWave_hasDerivAt_space_two (c₀ a v L t x : ℝ) :
    HasDerivAt (deriv fun y => travelingWave c₀ a v L t y)
      (-(a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L))) x := by
  have hder : ∀ y, deriv (fun y => travelingWave c₀ a v L t y) y =
      a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (y - v * t) / L) :=
    fun y => (travelingWave_hasDerivAt_space c₀ a v L t y).deriv
  have h1 : HasDerivAt (fun y : ℝ => y - v * t) 1 x := (hasDerivAt_id x).sub_const (v * t)
  have h2 : HasDerivAt (fun y : ℝ => 2 * Real.pi * (y - v * t)) ((2 * Real.pi) * 1) x :=
    HasDerivAt.const_mul (2 * Real.pi) h1
  have hphase : HasDerivAt (fun y : ℝ => 2 * Real.pi * (y - v * t) / L) (2 * Real.pi / L) x := by
    have h3 := h2.div_const L
    simpa using h3
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (2 * Real.pi * (y - v * t) / L))
      ((-Real.sin (2 * Real.pi * (x - v * t) / L)) * (2 * Real.pi / L)) x := by
    have h := (Real.hasDerivAt_cos (2 * Real.pi * (x - v * t) / L)).comp x hphase
    simpa only [Function.comp_def] using h
  have hexplicit : HasDerivAt
      (fun y : ℝ => a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (y - v * t) / L))
      (-(a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L))) x := by
    have hmul : HasDerivAt
        (fun y : ℝ => (a * (2 * Real.pi / L)) * Real.cos (2 * Real.pi * (y - v * t) / L))
        ((a * (2 * Real.pi / L)) *
          (((-Real.sin (2 * Real.pi * (x - v * t) / L)) * (2 * Real.pi / L)))) x :=
      HasDerivAt.const_mul (a * (2 * Real.pi / L)) hcos
    convert hmul using 1
    ring
  have heq : (deriv fun y => travelingWave c₀ a v L t y) =ᶠ[nhds x]
      (fun y : ℝ => a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (y - v * t) / L)) :=
    Filter.Eventually.of_forall hder
  exact hexplicit.congr_of_eventuallyEq heq

/-- Second time derivative: the time derivative of `c` has derivative
`-v² a (2π / L)² sin θ`. -/
lemma travelingWave_hasDerivAt_time_two (c₀ a v L t x : ℝ) :
    HasDerivAt (fun τ => deriv (fun τ' => travelingWave c₀ a v L τ' x) τ)
      (-(v ^ 2 * (a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L)))) t := by
  have hder : ∀ τ, deriv (fun τ' => travelingWave c₀ a v L τ' x) τ =
      (-(v * (a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (x - v * τ) / L)))) :=
    fun τ => (travelingWave_hasDerivAt_time c₀ a v L τ x).deriv
  have hmul : HasDerivAt (fun τ : ℝ => v * τ) (v * 1) t :=
    HasDerivAt.const_mul v (hasDerivAt_id t)
  have hsub : HasDerivAt (fun τ : ℝ => x - v * τ) (-(v * 1)) t :=
    HasDerivAt.const_sub x hmul
  have h2 : HasDerivAt (fun τ : ℝ => 2 * Real.pi * (x - v * τ)) ((2 * Real.pi) * (-(v * 1))) t :=
    HasDerivAt.const_mul (2 * Real.pi) hsub
  have hphase : HasDerivAt (fun τ : ℝ => 2 * Real.pi * (x - v * τ) / L)
      (-(v * (2 * Real.pi / L))) t := by
    have h3 := h2.div_const L
    convert h3 using 1
    ring
  have hcos : HasDerivAt (fun τ : ℝ => Real.cos (2 * Real.pi * (x - v * τ) / L))
      ((-Real.sin (2 * Real.pi * (x - v * t) / L)) * (-(v * (2 * Real.pi / L)))) t := by
    have h := (Real.hasDerivAt_cos (2 * Real.pi * (x - v * t) / L)).comp t hphase
    simpa only [Function.comp_def] using h
  have hinner : HasDerivAt
      (fun τ : ℝ => (a * (2 * Real.pi / L)) * Real.cos (2 * Real.pi * (x - v * τ) / L))
      ((a * (2 * Real.pi / L)) *
        (((-Real.sin (2 * Real.pi * (x - v * t) / L)) * (-(v * (2 * Real.pi / L)))))) t :=
    HasDerivAt.const_mul (a * (2 * Real.pi / L)) hcos
  have hmid : HasDerivAt
      (fun τ : ℝ => v * ((a * (2 * Real.pi / L)) * Real.cos (2 * Real.pi * (x - v * τ) / L)))
      (v * ((a * (2 * Real.pi / L)) *
        (((-Real.sin (2 * Real.pi * (x - v * t) / L)) * (-(v * (2 * Real.pi / L))))))) t :=
    HasDerivAt.const_mul v hinner
  have hneg : HasDerivAt
      (fun τ : ℝ => -(v * ((a * (2 * Real.pi / L)) * Real.cos (2 * Real.pi * (x - v * τ) / L))))
      (-(v * ((a * (2 * Real.pi / L)) *
        (((-Real.sin (2 * Real.pi * (x - v * t) / L)) * (-(v * (2 * Real.pi / L)))))))) t := by
    have h := hmid.neg
    simpa only [Pi.neg_def] using h
  have hexplicit : HasDerivAt
      (fun τ : ℝ => (-(v * (a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (x - v * τ) / L)))))
      (-(v ^ 2 * (a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L)))) t := by
    convert hneg using 1
    ring
  have heq : (fun τ => deriv (fun τ' => travelingWave c₀ a v L τ' x) τ) =ᶠ[nhds t]
      (fun τ : ℝ => (-(v * (a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (x - v * τ) / L))))) :=
    Filter.Eventually.of_forall hder
  exact hexplicit.congr_of_eventuallyEq heq

/-! ## E. Advection, periodicity and positivity -/

/-- The traveling wave solves the advection equation `∂ₜc + v ∂ₓc = 0` at every point. -/
lemma travelingWave_advection (c₀ a v L t x : ℝ) :
    deriv (fun τ => travelingWave c₀ a v L τ x) t +
      v * deriv (fun y => travelingWave c₀ a v L t y) x = 0 := by
  have ht : deriv (fun τ => travelingWave c₀ a v L τ x) t =
      (-(v * (a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (x - v * t) / L)))) :=
    (travelingWave_hasDerivAt_time c₀ a v L t x).deriv
  have hs : deriv (fun y => travelingWave c₀ a v L t y) x =
      (a * (2 * Real.pi / L) * Real.cos (2 * Real.pi * (x - v * t) / L)) :=
    (travelingWave_hasDerivAt_space c₀ a v L t x).deriv
  rw [ht, hs]
  ring

/-- The traveling wave has spatial period `L` at every time. -/
lemma travelingWave_periodic {L : ℝ} (hL : L ≠ 0) (c₀ a v t : ℝ) :
    Function.Periodic (travelingWave c₀ a v L t) L := by
  intro x
  show travelingWave c₀ a v L t (x + L) = travelingWave c₀ a v L t x
  simp only [travelingWave]
  have harg : 2 * Real.pi * (x + L - v * t) / L = 2 * Real.pi * (x - v * t) / L + 2 * Real.pi := by
    field_simp
    ring
  rw [harg]
  have h := Real.sin_periodic (2 * Real.pi * (x - v * t) / L)
  rw [h]

/-- The traveling wave is bounded below by `c₀ - |a|`. -/
lemma travelingWave_ge (c₀ a v L t x : ℝ) : c₀ - |a| ≤ travelingWave c₀ a v L t x := by
  simp only [travelingWave]
  have hsin : |Real.sin (2 * Real.pi * (x - v * t) / L)| ≤ 1 := Real.abs_sin_le_one _
  have hmul : |a * Real.sin (2 * Real.pi * (x - v * t) / L)| ≤ |a| := by
    calc |a * Real.sin (2 * Real.pi * (x - v * t) / L)|
        = |a| * |Real.sin (2 * Real.pi * (x - v * t) / L)| := abs_mul _ _
      _ ≤ |a| * 1 := by
            apply mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
      _ = |a| := mul_one _
  have hneg : -|a| ≤ a * Real.sin (2 * Real.pi * (x - v * t) / L) := by
    have h := neg_abs_le (a * Real.sin (2 * Real.pi * (x - v * t) / L))
    linarith
  linarith

/-- Positivity: when `|a| < c₀` the traveling wave is strictly positive everywhere. -/
lemma travelingWave_pos {c₀ a : ℝ} (h : |a| < c₀) (v L t x : ℝ) :
    0 < travelingWave c₀ a v L t x := by
  have hge := travelingWave_ge c₀ a v L t x
  linarith

/-! ## F. Second-derivative bounds -/

/-- The second spatial derivative is bounded by `M = |a| (2π / L)²` everywhere. -/
lemma travelingWave_space_bound (c₀ a v L t x : ℝ) :
    |iteratedDeriv 2 (fun y => travelingWave c₀ a v L t y) x| ≤
      |a| * (2 * Real.pi / L) ^ 2 := by
  have h2 : iteratedDeriv 2 (fun y => travelingWave c₀ a v L t y) x =
      (-(a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L))) := by
    have h1 : iteratedDeriv 1 (fun y => travelingWave c₀ a v L t y) =
        deriv (fun y => travelingWave c₀ a v L t y) := by
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    have hder := (travelingWave_hasDerivAt_space_two c₀ a v L t x).deriv
    have hiter : iteratedDeriv 2 (fun y => travelingWave c₀ a v L t y) =
        deriv (iteratedDeriv 1 (fun y => travelingWave c₀ a v L t y)) := by
      simp [iteratedDeriv_succ]
    rw [hiter, h1]
    exact hder
  rw [h2]
  have hsin : |Real.sin (2 * Real.pi * (x - v * t) / L)| ≤ 1 := Real.abs_sin_le_one _
  have hsq : 0 ≤ (2 * Real.pi / L) ^ 2 := sq_nonneg _
  calc |-(a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L))|
      = |a| * ((2 * Real.pi / L) ^ 2 * |Real.sin (2 * Real.pi * (x - v * t) / L)|) := by
        rw [abs_neg]
        rw [abs_mul, abs_mul, abs_of_nonneg hsq]
        ring
    _ ≤ |a| * ((2 * Real.pi / L) ^ 2 * 1) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left hsin hsq
    _ = |a| * (2 * Real.pi / L) ^ 2 := by ring

/-- The second time derivative is bounded by `v² M`, `M = |a| (2π / L)²`, everywhere. -/
lemma travelingWave_time_bound (c₀ a v L t x : ℝ) :
    |iteratedDeriv 2 (fun τ => travelingWave c₀ a v L τ x) t| ≤
      v ^ 2 * (|a| * (2 * Real.pi / L) ^ 2) := by
  have h2 : iteratedDeriv 2 (fun τ => travelingWave c₀ a v L τ x) t =
      (-(v ^ 2 * (a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L)))) := by
    have h1 : iteratedDeriv 1 (fun τ => travelingWave c₀ a v L τ x) =
        deriv (fun τ => travelingWave c₀ a v L τ x) := by
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    have hder := (travelingWave_hasDerivAt_time_two c₀ a v L t x).deriv
    have hiter : iteratedDeriv 2 (fun τ => travelingWave c₀ a v L τ x) =
        deriv (iteratedDeriv 1 (fun τ => travelingWave c₀ a v L τ x)) := by
      simp [iteratedDeriv_succ]
    rw [hiter, h1]
    exact hder
  rw [h2]
  have hsin : |Real.sin (2 * Real.pi * (x - v * t) / L)| ≤ 1 := Real.abs_sin_le_one _
  have hsq : 0 ≤ (2 * Real.pi / L) ^ 2 := sq_nonneg _
  have hv : 0 ≤ v ^ 2 := sq_nonneg _
  calc |-(v ^ 2 * (a * (2 * Real.pi / L) ^ 2 * Real.sin (2 * Real.pi * (x - v * t) / L)))|
      = v ^ 2 * (|a| * ((2 * Real.pi / L) ^ 2 * |Real.sin (2 * Real.pi * (x - v * t) / L)|)) := by
        rw [abs_neg]
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hv, abs_of_nonneg hsq]
        ring
    _ ≤ v ^ 2 * (|a| * ((2 * Real.pi / L) ^ 2 * 1)) := by
          apply mul_le_mul_of_nonneg_left _ hv
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hsin hsq
    _ = v ^ 2 * (|a| * (2 * Real.pi / L) ^ 2) := by ring

/-! ## G. Failure of strict positivity -/

/-- Without `|a| < c₀` positivity fails: if `c₀ ≤ |a|` and `L ≠ 0`, then at every time the wave
takes a nonpositive value. -/
lemma travelingWave_exists_nonpos {c₀ a L : ℝ} (hL : L ≠ 0) (h : c₀ ≤ |a|) (v t : ℝ) :
    ∃ x, travelingWave c₀ a v L t x ≤ 0 := by
  by_cases ha : 0 ≤ a
  · use v * t - L / 4
    simp only [travelingWave]
    have harg : 2 * Real.pi * ((v * t - L / 4) - v * t) / L = -(Real.pi / 2) := by
      field_simp
      ring
    rw [harg]
    have hsin : Real.sin (-(Real.pi / 2)) = -1 := by
      rw [Real.sin_neg, Real.sin_pi_div_two]
    rw [hsin]
    have habs : |a| = a := abs_of_nonneg ha
    linarith
  · have ha' : a < 0 := not_le.mp ha
    use v * t + L / 4
    simp only [travelingWave]
    have harg : 2 * Real.pi * ((v * t + L / 4) - v * t) / L = Real.pi / 2 := by
      field_simp
      ring
    rw [harg, Real.sin_pi_div_two]
    have habs : |a| = -a := abs_of_neg ha'
    linarith

end AdvectionError
