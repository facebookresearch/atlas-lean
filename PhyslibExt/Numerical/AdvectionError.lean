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

import MathlibExt.Analysis.Calculus.FirstOrderPropagationRemainder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Periodic face-flux advection: the upwind update, a traveling wave and its nodal error

The conservative finite-volume step for constant-speed scalar advection on a uniform periodic
grid, written with physical face fluxes and cell masses, is the canonical periodic upwind
update. A smooth traveling sine wave solves the continuous advection equation, with explicit
positivity and second-derivative bounds. Sampled at the grid nodes, the wave has an explicit
upwind truncation error; the update is nonexpansive in the maximum norm under the CFL
condition, so the nodal error of a numerical solution grows at most linearly in the number of
steps.

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

Parts H-L sample the wave on the grid: `ncells` uniform periodic cells of `[0, L)` with spacing
`dx = L / ncells`, node `j : ZMod ncells` at `x_j = j.val * dx` and time level `n` at
`t_n = n * dt`. The samples `w_j^n = c(t_n, x_j)` are actual point values, not cell averages,
and by periodicity the wrapped upstream neighbour of node `0` is the wave one cell upstream.

* Truncation. Second-order Taylor defects in time and in space, with the first-order terms
  cancelled by the advection equation and `ν dx = v dt`, give
  `|w_j^(n+1) - ((1 - ν) w_j^n + ν w_(j-1)^n)| ≤ dt * M * (v² dt + v dx) / 2` for `ν ≥ 0`.
* Stability. For `0 ≤ ν ≤ 1` each updated value is a convex combination of two old values, so
  the update does not increase the maximum nodal modulus.
* Accumulation. For a numerical solution `u` of the same recurrence the nodal error
  `E_n = maxⱼ |u_j^n - w_j^n|` satisfies `E_N ≤ E_0 + N * dt * M * (v² dt + v dx) / 2`, hence
  `E_N ≤ E_0 + T * M * (v² dt + v dx) / 2` whenever `N * dt ≤ T`.

These error bounds hold only for this smooth wave and under the CFL condition; nonsmooth data
and shocks have no second-derivative bound.

All quantities are exact real coordinates in one consistent unit system. Nonperiodic boundaries
and wells, moving meshes, reconstruction, cell averages, between-node norms and floating-point
roundoff are not treated.

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
- `AdvectionError.sampledWave_sub_one`: the wrapped upstream neighbour is the sample at
  `x_j - dx`.
- `AdvectionError.travelingWave_time_taylor`, `AdvectionError.travelingWave_space_taylor`:
  second-order Taylor defects of the wave.
- `AdvectionError.upwind_truncation_le`: the nodal truncation bound
  `dt * M * (v² dt + v dx) / 2`.
- `AdvectionError.abs_convex_combination_le`, `AdvectionError.upwind_norm_le`: max-norm
  nonexpansiveness for `0 ≤ ν ≤ 1`.
- `AdvectionError.upwind_error_le`, `AdvectionError.upwind_error_le_of_mul_le`: the accumulated
  nodal error after `N` steps and at a final time `T ≥ N * dt`.

## iii. Table of contents

- A. Face flux and the conservative step
- B. Identification with the upwind update
- C. Conservation and positivity
- D. The traveling wave and its derivatives
- E. Advection, periodicity and positivity
- F. Second-derivative bounds
- G. Failure of strict positivity
- H. Point samples on the periodic nodes
- I. Second-order Taylor defects of the wave
- J. Local truncation error at the nodes
- K. Max-norm nonexpansiveness of the update
- L. Error accumulation

## iv. References

- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press
  (2002), Chapter 2: the advection equation and its traveling-wave solutions; Chapter 4:
  conservative finite-volume updates, the upwind flux for advection and the CFL condition;
  Chapter 8: local truncation error, stability in the maximum norm and the error recursion.
- R. J. LeVeque, *Finite Difference Methods for Ordinary and Partial Differential Equations*,
  SIAM (2007), Chapter 10: the upwind method for advection and its truncation error.
- `EarthScience.upwind_nonneg` and `EarthScience.upwind_sum_eq`
  (`PhyslibExt.EarthScience.UpwindScheme`).
- Mathlib's `Real.hasDerivAt_sin` and `Real.hasDerivAt_cos`.
- `MathlibExt.Analysis.first_order_propagation_remainder_bound`
  (`MathlibExt.Analysis.Calculus.FirstOrderPropagationRemainder`): the first-order Taylor
  remainder bound behind the nodal truncation error.
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

/-! ## H. Point samples on the periodic nodes -/

/-- The point sample `w_j^n = c(n * dt, j * dx)` of the traveling wave on `ncells` uniform
periodic cells of `[0, L)`, `dx = L / ncells`: node `j : ZMod ncells` sits at
`x_j = j.val * dx` and time level `n` at `t_n = n * dt`. -/
noncomputable def sampledWave (c₀ a v L dt : ℝ) (ncells n : ℕ) [NeZero ncells]
    (j : ZMod ncells) : ℝ :=
  travelingWave c₀ a v L (n * dt) (j.val * (L / ncells))

/-- The wrapped upstream neighbour is an actual point sample one cell upstream: by spatial
periodicity `w_(j-1)^n = c(t_n, x_j - dx)`, also at `j = 0`, where `j - 1` is the last node. -/
lemma sampledWave_sub_one {ncells : ℕ} [NeZero ncells] {L : ℝ} (hL : L ≠ 0)
    (c₀ a v dt : ℝ) (n : ℕ) (j : ZMod ncells) :
    sampledWave c₀ a v L dt ncells n (j - 1) =
      travelingWave c₀ a v L (n * dt) (j.val * (L / ncells) - L / ncells) := by
  have hnne : ncells ≠ 0 := NeZero.ne ncells
  have hnpos : 0 < ncells := Nat.pos_of_ne_zero hnne
  have hncast : (ncells : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnne
  have hneg1 : (-1 : ZMod ncells).val = ncells - 1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnne
    rw [hm, ZMod.val_neg_one]
    omega
  have hsub : (j - 1 : ZMod ncells).val = if j = 0 then ncells - 1 else j.val - 1 := by
    rw [sub_eq_add_neg, ZMod.val_add, hneg1]
    split_ifs with hj
    · subst hj
      rw [ZMod.val_zero, zero_add, Nat.mod_eq_of_lt]
      omega
    · have hjv : 1 ≤ j.val := by
        have hne : j.val ≠ 0 := fun h => hj ((ZMod.val_eq_zero j).mp h)
        omega
      have hlt : j.val - 1 < ncells := by
        have := ZMod.val_lt j
        omega
      have heq : j.val + (ncells - 1) = (j.val - 1) + ncells * 1 := by omega
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  change travelingWave c₀ a v L (n * dt) ((j - 1).val * (L / ncells)) =
    travelingWave c₀ a v L (n * dt) (j.val * (L / ncells) - L / ncells)
  rw [hsub]
  split_ifs with hj
  · subst hj
    rw [ZMod.val_zero]
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hnne)]
    have hx : ((ncells : ℝ) - 1) * (L / ncells) = 0 * (L / ncells) - L / ncells + L := by
      field_simp
      ring
    rw [hx]
    exact travelingWave_periodic hL c₀ a v (n * dt) _
  · have hjv : 1 ≤ j.val := by
      have hne : j.val ≠ 0 := fun h => hj ((ZMod.val_eq_zero j).mp h)
      omega
    have hx : ((j.val - 1 : ℕ) : ℝ) * (L / ncells) =
        (j.val : ℝ) * (L / ncells) - L / ncells := by
      rw [Nat.cast_sub hjv]
      ring
    rw [hx]

/-! ## I. Second-order Taylor defects of the wave -/

/-- Temporal Taylor defect: for every step `h`,
`|c(t + h, x) - c(t, x) - h ∂ₜc(t, x)| ≤ v² M h² / 2` with `M = |a| (2π / L)²`. -/
lemma travelingWave_time_taylor (c₀ a v L t x h : ℝ) :
    |travelingWave c₀ a v L (t + h) x - travelingWave c₀ a v L t x -
        h * deriv (fun τ => travelingWave c₀ a v L τ x) t| ≤
      v ^ 2 * (|a| * (2 * Real.pi / L) ^ 2) * h ^ 2 / 2 := by
  have hp : ContDiff ℝ 2 fun τ : ℝ => (τ, x) := contDiff_id.prodMk contDiff_const
  have hf : ContDiff ℝ 2 (fun τ => travelingWave c₀ a v L τ x) := by
    simpa [Function.comp_def] using (travelingWave_contDiff c₀ a v L).comp hp
  have h2 : iteratedDeriv 2 (fun τ => travelingWave c₀ a v L τ x) =
      deriv (deriv fun τ => travelingWave c₀ a v L τ x) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hT := MathlibExt.Analysis.first_order_propagation_remainder_bound hf
    (fun τ => by rw [← h2]; exact travelingWave_time_bound c₀ a v L τ x) t h
  calc _ = |travelingWave c₀ a v L (t + h) x - travelingWave c₀ a v L t x -
        deriv (fun τ => travelingWave c₀ a v L τ x) t * h| := by rw [mul_comm h]
    _ ≤ _ := hT
    _ = _ := by ring

/-- Spatial Taylor defect one step upstream: for every step `h`,
`|c(t, x - h) - c(t, x) + h ∂ₓc(t, x)| ≤ M h² / 2` with `M = |a| (2π / L)²`. -/
lemma travelingWave_space_taylor (c₀ a v L t x h : ℝ) :
    |travelingWave c₀ a v L t (x - h) - travelingWave c₀ a v L t x +
        h * deriv (fun y => travelingWave c₀ a v L t y) x| ≤
      |a| * (2 * Real.pi / L) ^ 2 * h ^ 2 / 2 := by
  have hp : ContDiff ℝ 2 fun y : ℝ => (t, y) := contDiff_const.prodMk contDiff_id
  have hf : ContDiff ℝ 2 (fun y => travelingWave c₀ a v L t y) := by
    simpa [Function.comp_def] using (travelingWave_contDiff c₀ a v L).comp hp
  have h2 : iteratedDeriv 2 (fun y => travelingWave c₀ a v L t y) =
      deriv (deriv fun y => travelingWave c₀ a v L t y) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hT := MathlibExt.Analysis.first_order_propagation_remainder_bound hf
    (fun y => by rw [← h2]; exact travelingWave_space_bound c₀ a v L t y) x (-h)
  rw [← sub_eq_add_neg] at hT
  calc _ = |travelingWave c₀ a v L t (x - h) - travelingWave c₀ a v L t x -
        deriv (fun y => travelingWave c₀ a v L t y) x * -h| := by ring_nf
    _ ≤ _ := hT
    _ = _ := by ring

/-! ## J. Local truncation error at the nodes -/

/-- Nodal truncation error of the upwind update on the point samples: with `dx = L / ncells`,
Courant number `ν = v * dt / dx ≥ 0` and `M = |a| (2π / L)²`, at every node, the wrapped one
included, `|w_j^(n+1) - ((1 - ν) w_j^n + ν w_(j-1)^n)| ≤ dt * M * (v² dt + v dx) / 2`. -/
lemma upwind_truncation_le {ncells : ℕ} [NeZero ncells] {c₀ a v L dt : ℝ} (hL : 0 < L)
    (hdt : 0 < dt) (hν : 0 ≤ v * dt / (L / ncells)) (n : ℕ) (j : ZMod ncells) :
    |sampledWave c₀ a v L dt ncells (n + 1) j -
        ((1 - v * dt / (L / ncells)) * sampledWave c₀ a v L dt ncells n j +
          v * dt / (L / ncells) * sampledWave c₀ a v L dt ncells n (j - 1))| ≤
      dt * (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2 := by
  have hnne : ncells ≠ 0 := NeZero.ne ncells
  have hnpos : 0 < (ncells : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnne)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hncast : (ncells : ℝ) ≠ 0 := ne_of_gt hnpos
  have hdx : 0 < L / (ncells : ℝ) := div_pos hL hnpos
  have hdxne : L / (ncells : ℝ) ≠ 0 := ne_of_gt hdx
  have hcast : ((n + 1 : ℕ) : ℝ) * dt = (n : ℝ) * dt + dt := by push_cast; ring
  have hw1 : sampledWave c₀ a v L dt ncells (n + 1) j =
      travelingWave c₀ a v L ((n : ℝ) * dt + dt) ((j.val : ℝ) * (L / ncells)) := by
    unfold sampledWave
    rw [hcast]
  have hw2 : sampledWave c₀ a v L dt ncells n j =
      travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells)) := rfl
  have hw3 : sampledWave c₀ a v L dt ncells n (j - 1) =
      travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells) - L / ncells) :=
    sampledWave_sub_one hLne c₀ a v dt n j
  rw [hw1, hw2, hw3]
  have hA := travelingWave_time_taylor c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells)) dt
  have hB := travelingWave_space_taylor c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells))
    (L / ncells)
  have hadv := travelingWave_advection c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells))
  have hνdx : v * dt / (L / (ncells : ℝ)) * (L / (ncells : ℝ)) = v * dt :=
    div_mul_cancel₀ _ hdxne
  have hpde : dt * deriv (fun τ => travelingWave c₀ a v L τ ((j.val : ℝ) * (L / ncells)))
        ((n : ℝ) * dt)
      + v * dt / (L / ncells) * (L / ncells)
        * deriv (fun y => travelingWave c₀ a v L ((n : ℝ) * dt) y)
        ((j.val : ℝ) * (L / ncells)) = 0 := by
    rw [hνdx]
    linear_combination dt * hadv
  have hT : travelingWave c₀ a v L ((n : ℝ) * dt + dt) ((j.val : ℝ) * (L / ncells))
        - ((1 - v * dt / (L / ncells))
          * travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells))
          + v * dt / (L / ncells)
          * travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells) - L / ncells))
      = (travelingWave c₀ a v L ((n : ℝ) * dt + dt) ((j.val : ℝ) * (L / ncells))
        - travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells))
        - dt * deriv (fun τ => travelingWave c₀ a v L τ ((j.val : ℝ) * (L / ncells)))
          ((n : ℝ) * dt))
        - v * dt / (L / ncells)
          * (travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells) - L / ncells)
        - travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells))
        + (L / ncells) * deriv (fun y => travelingWave c₀ a v L ((n : ℝ) * dt) y)
          ((j.val : ℝ) * (L / ncells))) := by
    linear_combination hpde
  rw [hT]
  set A := travelingWave c₀ a v L ((n : ℝ) * dt + dt) ((j.val : ℝ) * (L / ncells))
    - travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells))
    - dt * deriv (fun τ => travelingWave c₀ a v L τ ((j.val : ℝ) * (L / ncells)))
      ((n : ℝ) * dt) with hAdef
  set B := travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells) - L / ncells)
    - travelingWave c₀ a v L ((n : ℝ) * dt) ((j.val : ℝ) * (L / ncells))
    + (L / ncells) * deriv (fun y => travelingWave c₀ a v L ((n : ℝ) * dt) y)
      ((j.val : ℝ) * (L / ncells)) with hBdef
  have hsplit : |A - v * dt / (L / ncells) * B| ≤ |A| + v * dt / (L / ncells) * |B| := by
    calc |A - v * dt / (L / ncells) * B| = |A + (-(v * dt / (L / ncells) * B))| := by
            rw [sub_eq_add_neg]
      _ ≤ |A| + |-(v * dt / (L / ncells) * B)| := abs_add_le _ _
      _ = |A| + v * dt / (L / ncells) * |B| := by rw [abs_neg, abs_mul, abs_of_nonneg hν]
  have hle : |A| + v * dt / (L / ncells) * |B|
      ≤ v ^ 2 * (|a| * (2 * Real.pi / L) ^ 2) * dt ^ 2 / 2
        + v * dt / (L / ncells) * ((|a| * (2 * Real.pi / L) ^ 2) * (L / ncells) ^ 2 / 2) :=
    add_le_add hA (mul_le_mul_of_nonneg_left hB hν)
  have hfin : v ^ 2 * (|a| * (2 * Real.pi / L) ^ 2) * dt ^ 2 / 2
        + v * dt / (L / ncells) * ((|a| * (2 * Real.pi / L) ^ 2) * (L / ncells) ^ 2 / 2)
      = dt * (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2 := by
    field_simp [hLne, hncast, hdxne]
  rw [← hfin]
  exact le_trans hsplit hle

/-! ## K. Max-norm nonexpansiveness of the update -/

/-- A convex combination is bounded by the larger modulus: `|(1 - ν) p + ν q| ≤ max |p| |q|`
for `0 ≤ ν ≤ 1`. -/
lemma abs_convex_combination_le {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (p q : ℝ) :
    |(1 - ν) * p + ν * q| ≤ max |p| |q| := by
  have h1 : (0:ℝ) ≤ 1 - ν := sub_nonneg.mpr hν1
  have htri : |(1 - ν) * p + ν * q| ≤ (1 - ν) * |p| + ν * |q| := by
    calc |(1 - ν) * p + ν * q| ≤ |(1 - ν) * p| + |ν * q| := abs_add_le _ _
      _ = (1 - ν) * |p| + ν * |q| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg hν0]
  have hp : |p| ≤ max |p| |q| := le_max_left _ _
  have hq : |q| ≤ max |p| |q| := le_max_right _ _
  have hle : (1 - ν) * |p| + ν * |q| ≤ (1 - ν) * max |p| |q| + ν * max |p| |q| :=
    add_le_add (mul_le_mul_of_nonneg_left hp h1) (mul_le_mul_of_nonneg_left hq hν0)
  have heq : (1 - ν) * max |p| |q| + ν * max |p| |q| = max |p| |q| := by ring
  linarith [htri, hle, heq]

/-- Max-norm nonexpansiveness: for `0 ≤ ν ≤ 1` the periodic upwind update does not increase the
maximum nodal modulus. -/
lemma upwind_norm_le {n : ℕ} [NeZero n] {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (e : ZMod n → ℝ) :
    ‖fun j => (1 - ν) * e j + ν * e (j - 1)‖ ≤ ‖e‖ := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro j
  change ‖(1 - ν) * e j + ν * e (j - 1)‖ ≤ ‖e‖
  rw [Real.norm_eq_abs]
  calc |(1 - ν) * e j + ν * e (j - 1)| ≤ max |e j| |e (j - 1)| :=
          abs_convex_combination_le hν0 hν1 _ _
    _ ≤ max ‖e‖ ‖e‖ := by
          apply max_le_max
          · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ _
          · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ _
    _ = ‖e‖ := max_self _

/-! ## L. Error accumulation -/

/-- Finite error induction: if `u` solves the same upwind recurrence on the same periodic nodes
with `0 ≤ ν ≤ 1`, the nodal error `E_k = maxⱼ |u_j^k - w_j^k|` satisfies
`E_N ≤ E_0 + N * (dt * M * (v² dt + v dx) / 2)`. -/
lemma upwind_error_le {ncells : ℕ} [NeZero ncells] {c₀ a v L dt : ℝ} (hL : 0 < L)
    (hdt : 0 < dt) (hν0 : 0 ≤ v * dt / (L / ncells)) (hν1 : v * dt / (L / ncells) ≤ 1)
    (u : ℕ → ZMod ncells → ℝ)
    (hu : ∀ k j, u (k + 1) j =
      (1 - v * dt / (L / ncells)) * u k j + v * dt / (L / ncells) * u k (j - 1))
    (N : ℕ) :
    ‖fun j => u N j - sampledWave c₀ a v L dt ncells N j‖ ≤
      ‖fun j => u 0 j - sampledWave c₀ a v L dt ncells 0 j‖ +
        N * (dt * (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2) := by
  have hnne : ncells ≠ 0 := NeZero.ne ncells
  have hnpos : 0 < (ncells : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnne)
  have hdx : 0 < L / (ncells : ℝ) := div_pos hL hnpos
  have hv : 0 ≤ v := by
    have hpos : 0 < dt / (L / (ncells : ℝ)) := div_pos hdt hdx
    have heq : v * dt / (L / (ncells : ℝ)) = v * (dt / (L / (ncells : ℝ))) := by ring
    have hν0' : 0 ≤ v * (dt / (L / (ncells : ℝ))) := by rw [← heq]; exact hν0
    by_contra hneg
    push Not at hneg
    have hlt := mul_neg_of_neg_of_pos hneg hpos
    linarith [hν0', hlt]
  set C := dt * (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2 with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; positivity
  induction N with
  | zero => simp
  | succ k ih =>
    have hTnorm : ‖fun j => sampledWave c₀ a v L dt ncells (k + 1) j -
          ((1 - v * dt / (L / ncells)) * sampledWave c₀ a v L dt ncells k j +
            v * dt / (L / ncells) * sampledWave c₀ a v L dt ncells k (j - 1))‖ ≤ C := by
      apply (pi_norm_le_iff_of_nonneg hC).mpr
      intro j
      change ‖sampledWave c₀ a v L dt ncells (k + 1) j -
          ((1 - v * dt / (L / ncells)) * sampledWave c₀ a v L dt ncells k j +
            v * dt / (L / ncells) * sampledWave c₀ a v L dt ncells k (j - 1))‖ ≤ C
      rw [Real.norm_eq_abs]
      have h := upwind_truncation_le (c₀ := c₀) (a := a) hL hdt hν0 k j
      rwa [← hCdef] at h
    have heq : (fun j => u (k + 1) j - sampledWave c₀ a v L dt ncells (k + 1) j)
        = (fun j => (1 - v * dt / (L / ncells))
            * (u k j - sampledWave c₀ a v L dt ncells k j)
            + v * dt / (L / ncells)
            * (u k (j - 1) - sampledWave c₀ a v L dt ncells k (j - 1)))
          - (fun j => sampledWave c₀ a v L dt ncells (k + 1) j -
            ((1 - v * dt / (L / ncells)) * sampledWave c₀ a v L dt ncells k j +
              v * dt / (L / ncells) * sampledWave c₀ a v L dt ncells k (j - 1))) := by
      funext j
      rw [hu k j]
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    refine le_trans (norm_sub_le _ _)
      (le_trans (add_le_add (upwind_norm_le hν0 hν1 _) hTnorm) ?_)
    have h2 : ‖fun j => u k j - sampledWave c₀ a v L dt ncells k j‖ + C
        ≤ (‖fun j => u 0 j - sampledWave c₀ a v L dt ncells 0 j‖ + (k : ℝ) * C) + C :=
      add_le_add ih (le_refl C)
    have h3 : (‖fun j => u 0 j - sampledWave c₀ a v L dt ncells 0 j‖ + (k : ℝ) * C) + C
        = ‖fun j => u 0 j - sampledWave c₀ a v L dt ncells 0 j‖ + ((k + 1 : ℕ) : ℝ) * C := by
      push_cast
      ring
    rw [h3] at h2
    exact h2

/-- The final-time bound: if `N * dt ≤ T`, then `E_N ≤ E_0 + T * M * (v² dt + v dx) / 2`. -/
lemma upwind_error_le_of_mul_le {ncells : ℕ} [NeZero ncells] {c₀ a v L dt : ℝ} (hL : 0 < L)
    (hdt : 0 < dt) (hν0 : 0 ≤ v * dt / (L / ncells)) (hν1 : v * dt / (L / ncells) ≤ 1)
    (u : ℕ → ZMod ncells → ℝ)
    (hu : ∀ k j, u (k + 1) j =
      (1 - v * dt / (L / ncells)) * u k j + v * dt / (L / ncells) * u k (j - 1))
    (N : ℕ) {T : ℝ} (hT : N * dt ≤ T) :
    ‖fun j => u N j - sampledWave c₀ a v L dt ncells N j‖ ≤
      ‖fun j => u 0 j - sampledWave c₀ a v L dt ncells 0 j‖ +
        T * (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2 := by
  have hnne : ncells ≠ 0 := NeZero.ne ncells
  have hnpos : 0 < (ncells : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnne)
  have hdx : 0 < L / (ncells : ℝ) := div_pos hL hnpos
  have hv : 0 ≤ v := by
    have hpos : 0 < dt / (L / (ncells : ℝ)) := div_pos hdt hdx
    have heq : v * dt / (L / (ncells : ℝ)) = v * (dt / (L / (ncells : ℝ))) := by ring
    have hν0' : 0 ≤ v * (dt / (L / (ncells : ℝ))) := by rw [← heq]; exact hν0
    by_contra hneg
    push Not at hneg
    have hlt := mul_neg_of_neg_of_pos hneg hpos
    linarith [hν0', hlt]
  have hM : 0 ≤ (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2 := by
    positivity
  have herr := upwind_error_le (c₀ := c₀) (a := a) hL hdt hν0 hν1 u hu N
  have hmul := mul_le_mul_of_nonneg_right hT hM
  have e1 : (N : ℝ) * (dt * (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2)
      = ((N : ℝ) * dt)
        * (((|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2)) := by
    ring
  have e2 : T * (|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2
      = T * (((|a| * (2 * Real.pi / L) ^ 2) * (v ^ 2 * dt + v * (L / ncells)) / 2)) := by
    ring
  rw [e2]
  rw [e1] at herr
  linarith [herr, hmul]

end AdvectionError
