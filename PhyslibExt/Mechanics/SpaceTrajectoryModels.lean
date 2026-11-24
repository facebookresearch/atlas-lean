/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PhyslibExt.Mechanics.PropulsionPorts
public import PhyslibExt.Units.EngineeringFrames

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Space trajectory models: the restricted three-body problem and a thrust-only rendezvous

Two models in normalized units: the circular restricted three-body problem in the frame that
rotates with its primaries (sections A-F), and a gravity-free, collinear thrust-only rendezvous
with independent terminal data (sections G-I).

## i. Overview

The restricted three-body problem (sections A-F). Two primaries of masses `1 - μ` and `μ` move on
circles about their barycenter, at unit separation and unit angular speed (gravitational constant
one). In the frame that rotates with them, `R(t) = rotZ t` about the third axis, the first
primary (mass `1 - μ`) sits at `(-μ, 0, 0)` and the second (mass `μ`) at `(1 - μ, 0, 0)`. A
massless particle with rotating-frame coordinates `(x, y, 0)` has inertial position
`X = R(t) (x, y, 0)`, by the frame dictionary's convention `x_I = o + R x_B` with the barycenter
as origin `o = 0`.

The effective potential is `Ω = (x² + y²) / 2 + (1 - μ) / r₁ + μ / r₂`, with `r₁`, `r₂` the
distances to the primaries. If `X` obeys Newton's law in the inertial frame under the attraction
of both primaries, then away from collisions the rotating coordinates obey
`x'' - 2 y' = Ω_x` and `y'' + 2 x' = Ω_y`, where `Ω_x`, `Ω_y` are the partial derivatives of `Ω`;
the equations are derived from the inertial field, not assumed. At the triangular points
`(1/2 - μ, ±√3/2)` both distances are one and both partial derivatives vanish, so they are
equilibria of the rotating equations: a particle there co-rotates with the primaries on a circle
that solves the inertial equations of motion. The primaries' own circular motion solves their
two-body equations, so unit angular speed is consistent with unit separation and unit total
mass.

The Jacobi function of a rotating-frame state with position `(x, y)` and velocity `(x', y')` is
`C = 2 Ω - (x'² + y'²)`. The Coriolis acceleration `-2 e₃ × v = (2 y', -2 x', 0)` of the
unit-rate rotation is perpendicular to the velocity `v = (x', y', 0)`, so its power vanishes, and
along a `C²` path that obeys the rotating equations with a thrust acceleration `(a_x, a_y)` the
derivative of `C` is `-2 (x' a_x + y' a_y)`, minus twice the thrust power. Without thrust `C` is
constant on every time interval on which the path avoids both primaries, in particular along the
inertial solutions of the two-primary field. Since `x'² + y'² ≥ 0`, an unforced trajectory with
Jacobi constant `C` stays in the region `2 Ω ≥ C`: a point with `2 Ω < C` is never reached on
it. For equal masses the state at the barycenter with velocity `(1, 0)` has `C = 3`, while the
triangular point `(0, √3/2)` has `2 Ω = 11/4`; a thrusting path from that state reaches the
triangular point, so the thrust-free hypothesis cannot be dropped.

Model inputs of sections A-F: the test particle is massless (it does not move the primaries); the
motion is in the primaries' orbital plane; collisions are excluded by `r₁, r₂ > 0`; the Jacobi
integral assumes no thrust or dissipation. The literature names the primaries larger and smaller
under the convention `0 < μ ≤ 1/2`; this module calls them first and second, and its lemmas hold
for every real `μ`, since no proof uses a range. Not covered: stability of the triangular points,
the collinear points, the spatial problem, and any limit from three positive masses.

The thrust-only rendezvous (sections G-I).
A gravity-free, collinear pilot of a thrust-only rendezvous in normalized units. The vehicle
starts from rest at the origin with mass `2`, expels propellant at the constant mass flow `1`
with exhaust speed `1` on the burn interval `[0, 1]`, so `m t = 2 - t` and the thrust is `1`.
The reduced variable-mass law `m v' = -ve * m'` of `PhyslibExt.Mechanics.PropulsionPorts` is
solved by `v t = log (2 / (2 - t))`, whose integral from the origin is
`x t = t + (2 - t) * log ((2 - t) / 2)`. A target coasting at the constant speed `log 2` along
`x_target t = 1 - 2 * log 2 + t * log 2` is met at `t = 1` with equal position `1 - log 2` and
equal velocity `log 2`, while the mass stays positive.

* The burn. `burnMass`, `burnVelocity` and `burnPosition` are the prescribed histories. On
  `[0, 1]` the mass is positive, the law holds with exhaust speed `1`, and its common value, the
  thrust, is `1`. The velocity gained, `log 2`, is the ideal rocket equation
  `velocity_increment_eq_log` at `ve = 1`, `m 0 / m 1 = 2`; the position is the integral of the
  velocity by the fundamental theorem of calculus.
* The target. `targetPosition` has its own terminal data, fixed explicitly and independently of
  the burn: speed `log 2` at all times and position `1 - log 2` at `t = 1`.
* Rendezvous. At `t = 1` both positions are `1 - log 2` and both have derivative `log 2`.
* Boundaries, checked in the test module. The mass vanishes at `t = 2`, outside the burn
  interval; there Lean's totalized `2 / 0 = 0` and `log 0 = 0` turn the velocity formula into
  the junk value `0`.

Signs: positions and velocities are measured along the thrust direction; the exhaust leaves
backward, `m' = -1 < 0`, and the vehicle speeds up, `v' = 1 / (2 - t) > 0`.

Model inputs of sections G-I: no gravity, drag or other external force; one line of motion; the
mass history, exhaust speed and target are fixed explicitly. This is not a general orbital
rendezvous, not a guidance law and not an optimality result; no empirical adequacy or vehicle
safety claim.

## ii. Key results

- `rotatingFrame`, `rotatingToInertial`, `primaryGravity`, `effectivePotential`: the rotating
  frame, the inertial field of the two primaries and the effective potential.
- `hasDerivAt_effectivePotential_fst`, `hasDerivAt_effectivePotential_snd`: the partial
  derivatives of `Ω` away from the primaries.
- `rotating_equations`: the rotating equations from the inertial two-primary field.
- `triangular_equilibrium`, `triangular_inertial_orbit`, `primaries_two_body`: the triangular
  points are collision-free equilibria and co-rotate on solutions of the inertial equations, and
  the primaries' circles solve their two-body equations.
- `jacobiConstant`, `coriolis_power_eq_zero`, `hasDerivAt_jacobiConstant`: the Jacobi function,
  the zero power of the Coriolis acceleration, and the rate `-2 (x' a_x + y' a_y)` of `C` under a
  thrust acceleration.
- `jacobiConstant_eq_of_rotating_equations`, `jacobiConstant_eq_of_newton`: the Jacobi integral
  along unforced solutions of the rotating equations and along inertial solutions.
- `jacobiConstant_le_two_effectivePotential`, `not_reach_of_two_effectivePotential_lt`: an
  unforced trajectory stays in `2 Ω ≥ C` and never reaches a point with `2 Ω < C`.
- `burnMass`, `burnVelocity`, `burnPosition`, `targetPosition`: the prescribed histories.
- `hasDerivAt_burnMass`, `burnMass_pos`, `hasDerivAt_burnVelocity`, `burn_law`: mass flow `1`,
  positive mass, the law with exhaust speed `1` and thrust `1`.
- `burn_initial`, `hasDerivAt_burnPosition`, `burnVelocity_increment`,
  `burnPosition_sub_eq_integral`: rest at the origin, `x' = v`, the ideal rocket equation and the
  displacement as the integral of the velocity.
- `hasDerivAt_targetPosition`, `rendezvous`: the target's constant speed and the matched
  terminal position and velocity at `t = 1`.
- The triangular points for `μ = 1/10`, the collision boundary, a non-equilibrium point, the
  Jacobi constant of a nonzero-velocity state with a point forbidden to it, a thrusting path that
  reaches that point, the nonzero burn and the excluded depletion time are checked in
  `PhyslibExtTest.Mechanics.SpaceTrajectoryModelsTest`.

## iii. Table of contents

- A. The rotating frame, the primaries and the effective potential
- B. The rotating equations
  - B.1. Private helpers
  - B.2. Derivation from the inertial field
- C. The triangular equilibria
- D. The Jacobi function and the Coriolis power
- E. Conservation along unforced solutions
- F. The forbidden region
- G. The prescribed burn
- H. Velocity and position histories
- I. The target and the rendezvous

## iv. References

- V. Szebehely, *Theory of Orbits: The Restricted Problem of Three Bodies*, ch. 1 and 4.
- C. D. Murray and S. F. Dermott, *Solar System Dynamics*, ch. 3: the circular restricted
  three-body problem, `Ω`, the equations of motion in the rotating frame, the Jacobi constant,
  zero-velocity curves and the Lagrangian points.
- G. P. Sutton and O. Biblarz, *Rocket Propulsion Elements*, 9th edition, chapters 2 and 4
  (thrust, effective exhaust velocity, ideal rocket equation).
- H. D. Curtis, *Orbital Mechanics for Engineering Students*, ch. 2 (the restricted three-body
  problem and the Lagrange points) and the rocket vehicle dynamics chapter.
- `PhyslibExt.Units.EngineeringFrames` (`bodyToInertial`, `rotZ`): the frame convention.
- `PhyslibExt.Mechanics.PropulsionPorts` (`velocity_increment_eq_log`).
-/

@[expose] public section

open scoped Matrix

namespace PhyslibExt.Mechanics.SpaceTrajectoryModels

open Set PhyslibExt.Mechanics.PropulsionPorts Units.EngineeringFrames

/-! ## A. The rotating frame, the primaries and the effective potential -/

/-- Orientation at time `t` of the frame rotating with the primaries: the rotation by the angle `t`
about the third axis (unit angular speed). -/
noncomputable def rotatingFrame (t : ℝ) : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨rotZ t, rotZ_mem_specialOrthogonalGroup t⟩

/-- Inertial position at time `t` of the point with rotating-frame coordinates `ξ`:
`X = R(t) ξ`, the frame dictionary's `x_I = o + R x_B` with the barycenter as origin `o = 0`. -/
noncomputable def rotatingToInertial (ξ : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  bodyToInertial 0 (rotatingFrame t) ξ

/-- Newtonian attraction `-m d / |d|³` toward a point mass `m` at relative position `d`, with
gravitational constant one and the Euclidean length `|d| = √(d ⬝ᵥ d)`. At `d = 0` Lean's
convention `x / 0 = 0` gives a meaningless value. -/
noncomputable def pointMassPull (m : ℝ) (d : Fin 3 → ℝ) : Fin 3 → ℝ :=
  -(m / Real.sqrt (d ⬝ᵥ d) ^ 3) • d

/-- Inertial gravitational field at the position `X` and time `t` of the two primaries: mass
`1 - μ` fixed at `(-μ, 0, 0)` and mass `μ` fixed at `(1 - μ, 0, 0)` in the rotating frame. -/
noncomputable def primaryGravity (μ t : ℝ) (X : Fin 3 → ℝ) : Fin 3 → ℝ :=
  pointMassPull (1 - μ) (X - rotatingToInertial ![-μ, 0, 0] t) +
    pointMassPull μ (X - rotatingToInertial ![1 - μ, 0, 0] t)

/-- Distance `r₁` from the rotating-frame point `(x, y)` to the first primary, of mass `1 - μ`, at
`(-μ, 0)`. -/
noncomputable def primaryDistOne (μ x y : ℝ) : ℝ := Real.sqrt ((x + μ) ^ 2 + y ^ 2)

/-- Distance `r₂` from the rotating-frame point `(x, y)` to the second primary, of mass `μ`, at
`(1 - μ, 0)`. -/
noncomputable def primaryDistTwo (μ x y : ℝ) : ℝ := Real.sqrt ((x - (1 - μ)) ^ 2 + y ^ 2)

/-- Effective potential `Ω = (x² + y²) / 2 + (1 - μ) / r₁ + μ / r₂` of the rotating frame. At a
primary Lean's convention `x / 0 = 0` gives a finite meaningless value. -/
noncomputable def effectivePotential (μ x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) / 2 + (1 - μ) / primaryDistOne μ x y + μ / primaryDistTwo μ x y

/-- The partial derivative `Ω_x = x - (1 - μ) (x + μ) / r₁³ - μ (x - 1 + μ) / r₂³` away from the
primaries. -/
lemma hasDerivAt_effectivePotential_fst {μ x y : ℝ} (h₁ : 0 < primaryDistOne μ x y)
    (h₂ : 0 < primaryDistTwo μ x y) :
    HasDerivAt (fun ξ => effectivePotential μ ξ y)
      (x - (1 - μ) * (x + μ) / primaryDistOne μ x y ^ 3 -
        μ * (x - (1 - μ)) / primaryDistTwo μ x y ^ 3) x := by
  have hq1 : (x + μ) ^ 2 + y ^ 2 ≠ 0 := by
    intro h
    unfold primaryDistOne at h₁
    rw [h, Real.sqrt_zero] at h₁
    exact lt_irrefl 0 h₁
  have hq2 : (x - (1 - μ)) ^ 2 + y ^ 2 ≠ 0 := by
    intro h
    unfold primaryDistTwo at h₂
    rw [h, Real.sqrt_zero] at h₂
    exact lt_irrefl 0 h₂
  have hd1 : HasDerivAt (fun ξ => (ξ + μ) ^ 2 + y ^ 2) (2 * (x + μ)) x := by
    have := (((hasDerivAt_id x).add_const μ).pow 2).add_const (y ^ 2)
    convert this using 1 <;> simp
  have hd2 : HasDerivAt (fun ξ => (ξ - (1 - μ)) ^ 2 + y ^ 2) (2 * (x - (1 - μ))) x := by
    have := (((hasDerivAt_id x).sub_const (1 - μ)).pow 2).add_const (y ^ 2)
    convert this using 1 <;> simp
  have hs1 : HasDerivAt (fun ξ => primaryDistOne μ ξ y)
      (2 * (x + μ) / (2 * primaryDistOne μ x y)) x := hd1.sqrt hq1
  have hs2 : HasDerivAt (fun ξ => primaryDistTwo μ ξ y)
      (2 * (x - (1 - μ)) / (2 * primaryDistTwo μ x y)) x := hd2.sqrt hq2
  have hp : HasDerivAt (fun ξ : ℝ => (ξ ^ 2 + y ^ 2) / 2) x x := by
    have := ((hasDerivAt_pow 2 x).add_const (y ^ 2)).div_const 2
    convert this using 1
    ring
  have h := (hp.add ((hasDerivAt_const x (1 - μ)).div hs1 h₁.ne')).add
    ((hasDerivAt_const x μ).div hs2 h₂.ne')
  unfold effectivePotential
  convert h using 1
  field_simp
  ring

/-- The partial derivative `Ω_y = y - (1 - μ) y / r₁³ - μ y / r₂³` away from the primaries. -/
lemma hasDerivAt_effectivePotential_snd {μ x y : ℝ} (h₁ : 0 < primaryDistOne μ x y)
    (h₂ : 0 < primaryDistTwo μ x y) :
    HasDerivAt (fun η => effectivePotential μ x η)
      (y - (1 - μ) * y / primaryDistOne μ x y ^ 3 - μ * y / primaryDistTwo μ x y ^ 3) y := by
  have hq1 : (x + μ) ^ 2 + y ^ 2 ≠ 0 := by
    intro h
    unfold primaryDistOne at h₁
    rw [h, Real.sqrt_zero] at h₁
    exact lt_irrefl 0 h₁
  have hq2 : (x - (1 - μ)) ^ 2 + y ^ 2 ≠ 0 := by
    intro h
    unfold primaryDistTwo at h₂
    rw [h, Real.sqrt_zero] at h₂
    exact lt_irrefl 0 h₂
  have hd1 : HasDerivAt (fun η => (x + μ) ^ 2 + η ^ 2) (2 * y) y := by
    have := (hasDerivAt_pow 2 y).const_add ((x + μ) ^ 2)
    convert this using 1
    simp
  have hd2 : HasDerivAt (fun η => (x - (1 - μ)) ^ 2 + η ^ 2) (2 * y) y := by
    have := (hasDerivAt_pow 2 y).const_add ((x - (1 - μ)) ^ 2)
    convert this using 1
    simp
  have hs1 : HasDerivAt (fun η => primaryDistOne μ x η)
      (2 * y / (2 * primaryDistOne μ x y)) y := hd1.sqrt hq1
  have hs2 : HasDerivAt (fun η => primaryDistTwo μ x η)
      (2 * y / (2 * primaryDistTwo μ x y)) y := hd2.sqrt hq2
  have hp : HasDerivAt (fun η : ℝ => (x ^ 2 + η ^ 2) / 2) y y := by
    have := ((hasDerivAt_pow 2 y).const_add (x ^ 2)).div_const 2
    convert this using 1
    ring
  have h := (hp.add ((hasDerivAt_const y (1 - μ)).div hs1 h₁.ne')).add
    ((hasDerivAt_const y μ).div hs2 h₂.ne')
  unfold effectivePotential
  convert h using 1
  field_simp
  ring

/-! ## B. The rotating equations -/

/-! ### B.1. Private helpers -/

/-- Components of the rotating-to-inertial map: `R(t) (a, b, c)` is
`(a cos t - b sin t, a sin t + b cos t, c)`. -/
private lemma rti_apply (a b c t : ℝ) :
    rotatingToInertial ![a, b, c] t =
      ![Real.cos t * a - Real.sin t * b, Real.sin t * a + Real.cos t * b, c] := by
  ext k
  fin_cases k <;> simp [rotatingToInertial, bodyToInertial, rotatingFrame, rotZ] <;> ring

/-- A point `(a, b, 0)` of the rotating plane in inertial components, as a combination of the
first two inertial axes. -/
private lemma rti_eq_smul (a b t : ℝ) :
    rotatingToInertial ![a, b, 0] t =
      (Real.cos t * a - Real.sin t * b) • ![(1 : ℝ), 0, 0] +
        (Real.sin t * a + Real.cos t * b) • ![(0 : ℝ), 1, 0] := by
  rw [rti_apply]
  ext k
  fin_cases k <;> simp

/-- The second time derivative of `R(s) (x(s), y(s), 0)` for `C²` coordinates, in the first two
inertial axes: the relative, Coriolis and centripetal terms of the unit-rate rotation. -/
private lemma deriv_deriv_rti {x y : ℝ → ℝ} (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y) (t : ℝ) :
    deriv (deriv fun s => rotatingToInertial ![x s, y s, 0] s) t =
      (Real.cos t * (deriv (deriv x) t - 2 * deriv y t - x t) -
          Real.sin t * (deriv (deriv y) t + 2 * deriv x t - y t)) • ![(1 : ℝ), 0, 0] +
        (Real.sin t * (deriv (deriv x) t - 2 * deriv y t - x t) +
          Real.cos t * (deriv (deriv y) t + 2 * deriv x t - y t)) • ![(0 : ℝ), 1, 0] := by
  have hx1 : ∀ s, HasDerivAt x (deriv x s) s :=
    fun s => (hx.differentiable (by norm_num) s).hasDerivAt
  have hy1 : ∀ s, HasDerivAt y (deriv y s) s :=
    fun s => (hy.differentiable (by norm_num) s).hasDerivAt
  have hx2 : ∀ s, HasDerivAt (deriv x) (deriv (deriv x) s) s :=
    fun s => (hx.differentiable_deriv_two s).hasDerivAt
  have hy2 : ∀ s, HasDerivAt (deriv y) (deriv (deriv y) s) s :=
    fun s => (hy.differentiable_deriv_two s).hasDerivAt
  have hfun : (fun s => rotatingToInertial ![x s, y s, 0] s) = fun s =>
      (Real.cos s * x s - Real.sin s * y s) • ![(1 : ℝ), 0, 0] +
        (Real.sin s * x s + Real.cos s * y s) • ![(0 : ℝ), 1, 0] := by
    funext s
    exact rti_eq_smul (x s) (y s) s
  have hd1 : ∀ s, HasDerivAt (fun s =>
      (Real.cos s * x s - Real.sin s * y s) • ![(1 : ℝ), 0, 0] +
        (Real.sin s * x s + Real.cos s * y s) • ![(0 : ℝ), 1, 0])
      ((Real.cos s * deriv x s - Real.sin s * deriv y s - Real.sin s * x s - Real.cos s * y s) •
          ![(1 : ℝ), 0, 0] +
        (Real.sin s * deriv x s + Real.cos s * deriv y s + Real.cos s * x s -
          Real.sin s * y s) • ![(0 : ℝ), 1, 0]) s := by
    intro s
    have hu := ((Real.hasDerivAt_cos s).mul (hx1 s)).sub ((Real.hasDerivAt_sin s).mul (hy1 s))
    have hw := ((Real.hasDerivAt_sin s).mul (hx1 s)).add ((Real.hasDerivAt_cos s).mul (hy1 s))
    have h := (hu.smul_const ![(1 : ℝ), 0, 0]).add (hw.smul_const ![(0 : ℝ), 1, 0])
    convert h using 2
    · ring_nf
    · ring_nf
  have hderiv : deriv (fun s =>
      (Real.cos s * x s - Real.sin s * y s) • ![(1 : ℝ), 0, 0] +
        (Real.sin s * x s + Real.cos s * y s) • ![(0 : ℝ), 1, 0]) = fun s =>
      (Real.cos s * deriv x s - Real.sin s * deriv y s - Real.sin s * x s - Real.cos s * y s) •
          ![(1 : ℝ), 0, 0] +
        (Real.sin s * deriv x s + Real.cos s * deriv y s + Real.cos s * x s -
          Real.sin s * y s) • ![(0 : ℝ), 1, 0] :=
    funext fun s => (hd1 s).deriv
  rw [hfun, hderiv]
  have hu2 := ((((Real.hasDerivAt_cos t).mul (hx2 t)).sub ((Real.hasDerivAt_sin t).mul (hy2 t))).sub
    ((Real.hasDerivAt_sin t).mul (hx1 t))).sub ((Real.hasDerivAt_cos t).mul (hy1 t))
  have hw2 := ((((Real.hasDerivAt_sin t).mul (hx2 t)).add ((Real.hasDerivAt_cos t).mul (hy2 t))).add
    ((Real.hasDerivAt_cos t).mul (hx1 t))).sub ((Real.hasDerivAt_sin t).mul (hy1 t))
  have h := (hu2.smul_const ![(1 : ℝ), 0, 0]).add (hw2.smul_const ![(0 : ℝ), 1, 0])
  have hd2 : HasDerivAt (fun s =>
      (Real.cos s * deriv x s - Real.sin s * deriv y s - Real.sin s * x s - Real.cos s * y s) •
          ![(1 : ℝ), 0, 0] +
        (Real.sin s * deriv x s + Real.cos s * deriv y s + Real.cos s * x s -
          Real.sin s * y s) • ![(0 : ℝ), 1, 0])
      ((Real.cos t * (deriv (deriv x) t - 2 * deriv y t - x t) -
          Real.sin t * (deriv (deriv y) t + 2 * deriv x t - y t)) • ![(1 : ℝ), 0, 0] +
        (Real.sin t * (deriv (deriv x) t - 2 * deriv y t - x t) +
          Real.cos t * (deriv (deriv y) t + 2 * deriv x t - y t)) • ![(0 : ℝ), 1, 0]) t := by
    convert h using 2
    · ring_nf
    · ring_nf
  exact hd2.deriv

/-- The rotation keeps squared distances between points of the rotating plane. -/
private lemma rti_sub_dot (a b p q t : ℝ) :
    (rotatingToInertial ![a, b, 0] t - rotatingToInertial ![p, q, 0] t) ⬝ᵥ
        (rotatingToInertial ![a, b, 0] t - rotatingToInertial ![p, q, 0] t) =
      (a - p) ^ 2 + (b - q) ^ 2 := by
  rw [rti_apply, rti_apply]
  simp [dotProduct, Fin.sum_univ_three]
  linear_combination ((a - p) ^ 2 + (b - q) ^ 2) * Real.cos_sq_add_sin_sq t

/-- The inertial field of the primaries at the point `(a, b, 0)` of the rotating plane, in the
first two inertial axes. -/
private lemma primaryGravity_rti (μ t a b : ℝ) :
    primaryGravity μ t (rotatingToInertial ![a, b, 0] t) =
      (Real.cos t * (-(1 - μ) * (a + μ) / primaryDistOne μ a b ^ 3 -
            μ * (a - (1 - μ)) / primaryDistTwo μ a b ^ 3) -
          Real.sin t * (-(1 - μ) * b / primaryDistOne μ a b ^ 3 -
            μ * b / primaryDistTwo μ a b ^ 3)) • ![(1 : ℝ), 0, 0] +
        (Real.sin t * (-(1 - μ) * (a + μ) / primaryDistOne μ a b ^ 3 -
            μ * (a - (1 - μ)) / primaryDistTwo μ a b ^ 3) +
          Real.cos t * (-(1 - μ) * b / primaryDistOne μ a b ^ 3 -
            μ * b / primaryDistTwo μ a b ^ 3)) • ![(0 : ℝ), 1, 0] := by
  have h1 := rti_sub_dot a b (-μ) 0 t
  have h2 := rti_sub_dot a b (1 - μ) 0 t
  unfold primaryGravity pointMassPull
  rw [h1, h2]
  have e1 : Real.sqrt ((a - -μ) ^ 2 + (b - 0) ^ 2) = primaryDistOne μ a b := by
    unfold primaryDistOne
    congr 1
    ring
  have e2 : Real.sqrt ((a - (1 - μ)) ^ 2 + (b - 0) ^ 2) = primaryDistTwo μ a b := by
    unfold primaryDistTwo
    congr 1
    ring
  rw [e1, e2, rti_apply, rti_apply, rti_apply]
  ext k
  fin_cases k <;> simp <;> ring

/-! ### B.2. Derivation from the inertial field -/

/-- The rotating equations of the restricted three-body problem, derived from the inertial field.
Let the rotating-frame coordinates `x`, `y` be `C²` and the particle avoid both primaries at time
`t`. If its inertial position `X(s) = R(s) (x(s), y(s), 0)` obeys Newton's law at `t` under the
attraction of the two primaries, then `x'' - 2 y' = Ω_x` and `y'' + 2 x' = Ω_y` at `t`, with the
partial derivatives of the effective potential. -/
lemma rotating_equations {μ t : ℝ} {x y : ℝ → ℝ} (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (h₁ : 0 < primaryDistOne μ (x t) (y t)) (h₂ : 0 < primaryDistTwo μ (x t) (y t))
    (hN : deriv (deriv fun s => rotatingToInertial ![x s, y s, 0] s) t =
      primaryGravity μ t (rotatingToInertial ![x t, y t, 0] t)) :
    deriv (deriv x) t - 2 * deriv y t = deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) ∧
      deriv (deriv y) t + 2 * deriv x t =
        deriv (fun η => effectivePotential μ (x t) η) (y t) := by
  have hA := deriv_deriv_rti hx hy t
  have hG := primaryGravity_rti μ t (x t) (y t)
  rw [hA, hG] at hN
  have h0 := congrFun hN 0
  have h1 := congrFun hN 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero,
    Matrix.smul_empty, Fin.isValue, Pi.add_apply, Matrix.cons_val_zero, add_zero, neg_sub,
    Matrix.cons_val_one, zero_add] at h0 h1
  have hcs := Real.cos_sq_add_sin_sq t
  have ha : deriv (deriv x) t - 2 * deriv y t - x t =
      -(1 - μ) * (x t + μ) / primaryDistOne μ (x t) (y t) ^ 3 -
        μ * (x t - (1 - μ)) / primaryDistTwo μ (x t) (y t) ^ 3 := by
    linear_combination Real.cos t * h0 + Real.sin t * h1 -
      (deriv (deriv x) t - 2 * deriv y t - x t -
        (-(1 - μ) * (x t + μ) / primaryDistOne μ (x t) (y t) ^ 3 -
          μ * (x t - (1 - μ)) / primaryDistTwo μ (x t) (y t) ^ 3)) * hcs
  have hb : deriv (deriv y) t + 2 * deriv x t - y t =
      -(1 - μ) * y t / primaryDistOne μ (x t) (y t) ^ 3 -
        μ * y t / primaryDistTwo μ (x t) (y t) ^ 3 := by
    linear_combination -Real.sin t * h0 + Real.cos t * h1 -
      (deriv (deriv y) t + 2 * deriv x t - y t -
        (-(1 - μ) * y t / primaryDistOne μ (x t) (y t) ^ 3 -
          μ * y t / primaryDistTwo μ (x t) (y t) ^ 3)) * hcs
  rw [(hasDerivAt_effectivePotential_fst h₁ h₂).deriv,
    (hasDerivAt_effectivePotential_snd h₁ h₂).deriv]
  constructor
  · linear_combination ha
  · linear_combination hb

/-! ## C. The triangular equilibria -/

/-- The triangular points `(1/2 - μ, s √3/2)`, `s = 1` and `s = -1`, are at unit distance from both
primaries (so collision-free), and both partial derivatives of the effective potential vanish
there: they are equilibria of the rotating equations. No stability is claimed. -/
lemma triangular_equilibrium (μ : ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    primaryDistOne μ (1 / 2 - μ) (s * (Real.sqrt 3 / 2)) = 1 ∧
      primaryDistTwo μ (1 / 2 - μ) (s * (Real.sqrt 3 / 2)) = 1 ∧
      HasDerivAt (fun ξ => effectivePotential μ ξ (s * (Real.sqrt 3 / 2))) 0 (1 / 2 - μ) ∧
      HasDerivAt (fun η => effectivePotential μ (1 / 2 - μ) η) 0 (s * (Real.sqrt 3 / 2)) := by
  have hs2 : s ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd1 : primaryDistOne μ (1 / 2 - μ) (s * (Real.sqrt 3 / 2)) = 1 := by
    unfold primaryDistOne
    rw [show (1 / 2 - μ + μ) ^ 2 + (s * (Real.sqrt 3 / 2)) ^ 2 = (1 : ℝ) by
      linear_combination (3 / 4) * hs2 + (s ^ 2 / 4) * h3]
    exact Real.sqrt_one
  have hd2 : primaryDistTwo μ (1 / 2 - μ) (s * (Real.sqrt 3 / 2)) = 1 := by
    unfold primaryDistTwo
    rw [show (1 / 2 - μ - (1 - μ)) ^ 2 + (s * (Real.sqrt 3 / 2)) ^ 2 = (1 : ℝ) by
      linear_combination (3 / 4) * hs2 + (s ^ 2 / 4) * h3]
    exact Real.sqrt_one
  have hp1 : 0 < primaryDistOne μ (1 / 2 - μ) (s * (Real.sqrt 3 / 2)) := by rw [hd1]; norm_num
  have hp2 : 0 < primaryDistTwo μ (1 / 2 - μ) (s * (Real.sqrt 3 / 2)) := by rw [hd2]; norm_num
  refine ⟨hd1, hd2, ?_, ?_⟩
  · have h := hasDerivAt_effectivePotential_fst hp1 hp2
    rw [hd1, hd2] at h
    convert h using 1
    ring
  · have h := hasDerivAt_effectivePotential_snd hp1 hp2
    rw [hd1, hd2] at h
    convert h using 1
    ring

/-- A particle fixed at a triangular point of the rotating frame moves on a circle in the inertial
frame, and that circle solves the inertial equations of motion under both primaries at every
time. -/
lemma triangular_inertial_orbit (μ : ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1) (t : ℝ) :
    deriv (deriv (rotatingToInertial ![1 / 2 - μ, s * (Real.sqrt 3 / 2), 0])) t =
      primaryGravity μ t (rotatingToInertial ![1 / 2 - μ, s * (Real.sqrt 3 / 2), 0] t) := by
  obtain ⟨hd1, hd2, -, -⟩ := triangular_equilibrium μ hs
  have hA := deriv_deriv_rti (x := fun _ => 1 / 2 - μ) (y := fun _ => s * (Real.sqrt 3 / 2))
    contDiff_const contDiff_const t
  simp only [deriv_const', deriv_const] at hA
  rw [hA, primaryGravity_rti, hd1, hd2]
  congr 2
  · ring
  · ring

/-- Model consistency: the primaries' circular motion at unit angular speed and unit separation
solves their two-body equations, each primary pulled by the other's mass. -/
lemma primaries_two_body (μ t : ℝ) :
    deriv (deriv (rotatingToInertial ![-μ, 0, 0])) t =
        pointMassPull μ (rotatingToInertial ![-μ, 0, 0] t - rotatingToInertial ![1 - μ, 0, 0] t) ∧
      deriv (deriv (rotatingToInertial ![1 - μ, 0, 0])) t =
        pointMassPull (1 - μ)
          (rotatingToInertial ![1 - μ, 0, 0] t - rotatingToInertial ![-μ, 0, 0] t) := by
  have hdist : ∀ c d : ℝ, (rotatingToInertial ![c, 0, 0] t - rotatingToInertial ![d, 0, 0] t) ⬝ᵥ
      (rotatingToInertial ![c, 0, 0] t - rotatingToInertial ![d, 0, 0] t) = (c - d) ^ 2 := by
    intro c d
    rw [rti_sub_dot]
    ring
  have hA := fun c : ℝ => deriv_deriv_rti (x := fun _ => c) (y := fun _ => (0 : ℝ))
    contDiff_const contDiff_const t
  simp only [deriv_const', deriv_const] at hA
  refine ⟨?_, ?_⟩
  · rw [hA, pointMassPull, hdist]
    rw [show (-μ - (1 - μ)) ^ 2 = (1 : ℝ) by ring, Real.sqrt_one, rti_eq_smul, rti_eq_smul]
    ext k
    fin_cases k <;> simp <;> ring
  · rw [hA, pointMassPull, hdist]
    rw [show (1 - μ - -μ) ^ 2 = (1 : ℝ) by ring, Real.sqrt_one, rti_eq_smul, rti_eq_smul]
    ext k
    fin_cases k <;> simp <;> ring

/-! ## D. The Jacobi function and the Coriolis power -/

/-- The Jacobi function `C = 2 Ω - (vx² + vy²)` of the rotating-frame state with position
`(x, y)` and velocity `(vx, vy)`. -/
noncomputable def jacobiConstant (μ x y vx vy : ℝ) : ℝ :=
  2 * effectivePotential μ x y - (vx ^ 2 + vy ^ 2)

/-- **The Coriolis power cancels.** For the unit angular velocity `e₃` of the rotating frame and
a velocity `v = (vx, vy, 0)` in the orbital plane, the Coriolis acceleration `-2 e₃ × v` is
`(2 vy, -2 vx, 0)`, the velocity terms of the rotating equations, and its power `v ⬝ (-2 e₃ × v)`
vanishes. -/
lemma coriolis_power_eq_zero (vx vy : ℝ) :
    -(2 : ℝ) • (![(0 : ℝ), 0, 1] ⨯₃ ![vx, vy, 0]) = ![2 * vy, -(2 * vx), 0] ∧
      ![vx, vy, 0] ⬝ᵥ (-(2 : ℝ) • (![(0 : ℝ), 0, 1] ⨯₃ ![vx, vy, 0])) = 0 := by
  constructor
  · rw [cross_apply]
    ext k
    fin_cases k <;> simp
  · have h := dot_cross_self ![(0 : ℝ), 0, 1] ![vx, vy, 0]
    rw [dotProduct_smul, h]
    simp

/-- **Jacobi derivative.** Let `x`, `y` be `C²` and let the particle avoid both primaries at time
`t`, where it obeys the rotating equations with the thrust acceleration `(ax, ay)`:
`x'' - 2 y' = Ω_x + ax` and `y'' + 2 x' = Ω_y + ay`. Then the Jacobi function along the path has
the derivative `-2 (x' ax + y' ay)` at `t`: the Coriolis power cancels, and only the thrust power
changes `C`. -/
lemma hasDerivAt_jacobiConstant {μ t ax ay : ℝ} {x y : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hy : ContDiff ℝ 2 y) (h₁ : 0 < primaryDistOne μ (x t) (y t))
    (h₂ : 0 < primaryDistTwo μ (x t) (y t))
    (hfx : deriv (deriv x) t - 2 * deriv y t =
      deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) + ax)
    (hfy : deriv (deriv y) t + 2 * deriv x t =
      deriv (fun η => effectivePotential μ (x t) η) (y t) + ay) :
    HasDerivAt (fun s => jacobiConstant μ (x s) (y s) (deriv x s) (deriv y s))
      (-2 * (deriv x t * ax + deriv y t * ay)) t := by
  have hx1 : HasDerivAt x (deriv x t) t := (hx.differentiable (by norm_num) t).hasDerivAt
  have hy1 : HasDerivAt y (deriv y t) t := (hy.differentiable (by norm_num) t).hasDerivAt
  have hx2 : HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    (hx.differentiable_deriv_two t).hasDerivAt
  have hy2 : HasDerivAt (deriv y) (deriv (deriv y) t) t :=
    (hy.differentiable_deriv_two t).hasDerivAt
  have hq1 : (x t + μ) ^ 2 + (y t) ^ 2 ≠ 0 := by
    intro h
    unfold primaryDistOne at h₁
    rw [h, Real.sqrt_zero] at h₁
    exact lt_irrefl 0 h₁
  have hq2 : (x t - (1 - μ)) ^ 2 + (y t) ^ 2 ≠ 0 := by
    intro h
    unfold primaryDistTwo at h₂
    rw [h, Real.sqrt_zero] at h₂
    exact lt_irrefl 0 h₂
  have hΩ : HasDerivAt (fun s => effectivePotential μ (x s) (y s))
      (deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) * deriv x t +
        deriv (fun η => effectivePotential μ (x t) η) (y t) * deriv y t) t := by
    have hd1 : HasDerivAt (fun s => (x s + μ) ^ 2 + (y s) ^ 2)
        (2 * (x t + μ) * deriv x t + 2 * (y t) * deriv y t) t := by
      have h := ((hx1.add_const μ).pow 2).add (hy1.pow 2)
      convert h using 1; simp
    have hd2 : HasDerivAt (fun s => (x s - (1 - μ)) ^ 2 + (y s) ^ 2)
        (2 * (x t - (1 - μ)) * deriv x t + 2 * (y t) * deriv y t) t := by
      have h := ((hx1.sub_const (1 - μ)).pow 2).add (hy1.pow 2)
      convert h using 1; simp
    have hs1 : HasDerivAt (fun s => primaryDistOne μ (x s) (y s))
        ((2 * (x t + μ) * deriv x t + 2 * (y t) * deriv y t) /
          (2 * primaryDistOne μ (x t) (y t))) t := hd1.sqrt hq1
    have hs2 : HasDerivAt (fun s => primaryDistTwo μ (x s) (y s))
        ((2 * (x t - (1 - μ)) * deriv x t + 2 * (y t) * deriv y t) /
          (2 * primaryDistTwo μ (x t) (y t))) t := hd2.sqrt hq2
    have hp : HasDerivAt (fun s => ((x s) ^ 2 + (y s) ^ 2) / 2)
        ((x t) * deriv x t + (y t) * deriv y t) t := by
      have h := ((hx1.pow 2).add (hy1.pow 2)).div_const 2
      convert h using 1
      ring
    have h := (hp.add ((hasDerivAt_const t (1 - μ)).div hs1 h₁.ne')).add
      ((hasDerivAt_const t μ).div hs2 h₂.ne')
    have hOx := (hasDerivAt_effectivePotential_fst h₁ h₂).deriv
    have hOy := (hasDerivAt_effectivePotential_snd h₁ h₂).deriv
    rw [hOx, hOy]
    unfold effectivePotential
    convert h using 1
    have h₁' := h₁.ne'
    have h₂' := h₂.ne'
    field_simp
    ring
  have hv : HasDerivAt (fun s => (deriv x s) ^ 2 + (deriv y s) ^ 2)
      (2 * deriv x t * deriv (deriv x) t + 2 * deriv y t * deriv (deriv y) t) t := by
    have h := (hx2.pow 2).add (hy2.pow 2)
    convert h using 1; simp
  have hC : HasDerivAt (fun s => 2 * effectivePotential μ (x s) (y s) -
      ((deriv x s) ^ 2 + (deriv y s) ^ 2))
      (2 * (deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) * deriv x t +
        deriv (fun η => effectivePotential μ (x t) η) (y t) * deriv y t) -
        (2 * deriv x t * deriv (deriv x) t + 2 * deriv y t * deriv (deriv y) t)) t :=
    (hΩ.const_mul 2).sub hv
  have hcor := coriolis_power_eq_zero (deriv x t) (deriv y t)
  have hpow := hcor.2
  rw [hcor.1] at hpow
  simp [dotProduct, Fin.sum_univ_three] at hpow
  unfold jacobiConstant
  convert hC using 1
  linear_combination (2 * deriv x t) * hfx + (2 * deriv y t) * hfy + 2 * hpow

/-! ## E. Conservation along unforced solutions -/

/-- **The Jacobi integral.** Let `x`, `y` be `C²`, avoid both primaries and obey the rotating
equations `x'' - 2 y' = Ω_x`, `y'' + 2 x' = Ω_y` at every time of `[t₀, t₁]`. Then the Jacobi
function is constant on `[t₀, t₁]`. -/
lemma jacobiConstant_eq_of_rotating_equations {μ t₀ t₁ : ℝ} {x y : ℝ → ℝ}
    (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (h₁ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistOne μ (x t) (y t))
    (h₂ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistTwo μ (x t) (y t))
    (hrot : ∀ t ∈ Icc t₀ t₁,
      deriv (deriv x) t - 2 * deriv y t = deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) ∧
        deriv (deriv y) t + 2 * deriv x t =
          deriv (fun η => effectivePotential μ (x t) η) (y t)) :
    ∀ t ∈ Icc t₀ t₁, jacobiConstant μ (x t) (y t) (deriv x t) (deriv y t) =
      jacobiConstant μ (x t₀) (y t₀) (deriv x t₀) (deriv y t₀) := by
  have hC0 : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt (fun s => jacobiConstant μ (x s) (y s) (deriv x s) (deriv y s)) 0 t := by
    intro t ht
    have h := hasDerivAt_jacobiConstant hx hy (h₁ t ht) (h₂ t ht)
      (show deriv (deriv x) t - 2 * deriv y t =
        deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) + 0 by
        rw [add_zero]; exact (hrot t ht).1)
      (show deriv (deriv y) t + 2 * deriv x t =
        deriv (fun η => effectivePotential μ (x t) η) (y t) + 0 by
        rw [add_zero]; exact (hrot t ht).2)
    simpa using h
  have hcont : ContinuousOn
      (fun s => jacobiConstant μ (x s) (y s) (deriv x s) (deriv y s)) (Icc t₀ t₁) :=
    fun t ht => (hC0 t ht).continuousAt.continuousWithinAt
  have hderiv : ∀ u ∈ Ico t₀ t₁, HasDerivWithinAt
      (fun s => jacobiConstant μ (x s) (y s) (deriv x s) (deriv y s)) 0 (Ici u) u :=
    fun u hu => (hC0 u (Ico_subset_Icc_self hu)).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hderiv

/-- **The Jacobi integral of an inertial solution.** Let `x`, `y` be `C²` and avoid both
primaries on `[t₀, t₁]`, and let the inertial position `X(s) = R(s) (x(s), y(s), 0)` obey
Newton's law under the attraction of the two primaries at every time of `[t₀, t₁]`. Then the
Jacobi function of the rotating coordinates is constant on `[t₀, t₁]`. -/
lemma jacobiConstant_eq_of_newton {μ t₀ t₁ : ℝ} {x y : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hy : ContDiff ℝ 2 y) (h₁ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistOne μ (x t) (y t))
    (h₂ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistTwo μ (x t) (y t))
    (hN : ∀ t ∈ Icc t₀ t₁, deriv (deriv fun s => rotatingToInertial ![x s, y s, 0] s) t =
      primaryGravity μ t (rotatingToInertial ![x t, y t, 0] t)) :
    ∀ t ∈ Icc t₀ t₁, jacobiConstant μ (x t) (y t) (deriv x t) (deriv y t) =
      jacobiConstant μ (x t₀) (y t₀) (deriv x t₀) (deriv y t₀) := by
  exact jacobiConstant_eq_of_rotating_equations hx hy h₁ h₂
    (fun t ht => rotating_equations hx hy (h₁ t ht) (h₂ t ht) (hN t ht))

/-! ## F. The forbidden region -/

/-- **Zero-velocity bound.** Under the hypotheses of `jacobiConstant_eq_of_rotating_equations`,
the trajectory stays in the region `2 Ω ≥ C` of its initial Jacobi constant `C`. -/
lemma jacobiConstant_le_two_effectivePotential {μ t₀ t₁ : ℝ} {x y : ℝ → ℝ}
    (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (h₁ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistOne μ (x t) (y t))
    (h₂ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistTwo μ (x t) (y t))
    (hrot : ∀ t ∈ Icc t₀ t₁,
      deriv (deriv x) t - 2 * deriv y t = deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) ∧
        deriv (deriv y) t + 2 * deriv x t =
          deriv (fun η => effectivePotential μ (x t) η) (y t)) :
    ∀ t ∈ Icc t₀ t₁, jacobiConstant μ (x t₀) (y t₀) (deriv x t₀) (deriv y t₀) ≤
      2 * effectivePotential μ (x t) (y t) := by
  intro t ht
  have hC := jacobiConstant_eq_of_rotating_equations hx hy h₁ h₂ hrot t ht
  have hsq : (0 : ℝ) ≤ (deriv x t) ^ 2 + (deriv y t) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  unfold jacobiConstant at hC ⊢
  linarith

/-- **A forbidden point is not reached.** Under the hypotheses of
`jacobiConstant_eq_of_rotating_equations`, a point `(a, b)` with `2 Ω(a, b) < C`, for the
initial Jacobi constant `C`, is not the position at any time of `[t₀, t₁]`; in particular it is
not the terminal point. -/
lemma not_reach_of_two_effectivePotential_lt {μ t₀ t₁ a b : ℝ} {x y : ℝ → ℝ}
    (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (h₁ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistOne μ (x t) (y t))
    (h₂ : ∀ t ∈ Icc t₀ t₁, 0 < primaryDistTwo μ (x t) (y t))
    (hrot : ∀ t ∈ Icc t₀ t₁,
      deriv (deriv x) t - 2 * deriv y t = deriv (fun ξ => effectivePotential μ ξ (y t)) (x t) ∧
        deriv (deriv y) t + 2 * deriv x t =
          deriv (fun η => effectivePotential μ (x t) η) (y t))
    (hab : 2 * effectivePotential μ a b <
      jacobiConstant μ (x t₀) (y t₀) (deriv x t₀) (deriv y t₀)) :
    ∀ t ∈ Icc t₀ t₁, ¬ (x t = a ∧ y t = b) := by
  intro t ht hcon
  obtain ⟨hxt, hyt⟩ := hcon
  have hle := jacobiConstant_le_two_effectivePotential hx hy h₁ h₂ hrot t ht
  rw [hxt, hyt] at hle
  linarith

/-! ## G. The prescribed burn -/

/-- The mass history `m t = 2 - t` of the normalized burn: initial mass `2` and propellant mass
flow `1`, so the mass falls from `2` to `1` on the burn interval `[0, 1]`. -/
def burnMass (t : ℝ) : ℝ := 2 - t

/-- The velocity history `v t = log (2 / (2 - t))` of the burn, from rest at `t = 0`. -/
noncomputable def burnVelocity (t : ℝ) : ℝ := Real.log (2 / (2 - t))

/-- The position history `x t = t + (2 - t) * log ((2 - t) / 2)` of the burn, from the origin at
`t = 0`. -/
noncomputable def burnPosition (t : ℝ) : ℝ := t + (2 - t) * Real.log ((2 - t) / 2)

/-- The target `x_target t = 1 - 2 * log 2 + t * log 2`, coasting at the constant speed `log 2`.
Its terminal data are fixed explicitly, independently of the burn. -/
noncomputable def targetPosition (t : ℝ) : ℝ := 1 - 2 * Real.log 2 + t * Real.log 2

/-- The mass flow is constant: `m' = -1` at every time. -/
lemma hasDerivAt_burnMass (t : ℝ) : HasDerivAt burnMass (-1) t := by
  have h1 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
  have h2 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h : HasDerivAt (fun i : ℝ => (2 : ℝ) - i) (0 - 1) t := h1.fun_sub h2
  have hderiv : (0 : ℝ) - 1 = -1 := by norm_num
  rw [hderiv] at h
  exact h

/-- The mass stays positive on the burn interval `[0, 1]`. -/
lemma burnMass_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < burnMass t := by
  rw [mem_Icc] at ht
  obtain ⟨-, h1⟩ := ht
  unfold burnMass
  linarith

/-- Before depletion (`t < 2`) the velocity has derivative `v' = 1 / (2 - t)`. -/
lemma hasDerivAt_burnVelocity {t : ℝ} (ht : t < 2) :
    HasDerivAt burnVelocity (1 / (2 - t)) t := by
  have hpos : (0 : ℝ) < 2 - t := by linarith
  have h2t : (2 : ℝ) - t ≠ 0 := ne_of_gt hpos
  have hne : (2 : ℝ) / (2 - t) ≠ 0 := div_ne_zero (by norm_num) h2t
  have hden : HasDerivAt (fun x : ℝ => (2 : ℝ) - x) (-1) t := hasDerivAt_burnMass t
  have hnum : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
  have hdiv : HasDerivAt (fun x : ℝ => (2 : ℝ) / (2 - x))
      ((0 * (2 - t) - 2 * (-1)) / (2 - t) ^ 2) t :=
    hnum.fun_div hden h2t
  have hlog : HasDerivAt (fun y : ℝ => Real.log (2 / (2 - y)))
      ((0 * (2 - t) - 2 * (-1)) / (2 - t) ^ 2 / (2 / (2 - t))) t :=
    hdiv.log hne
  have hderiv : (0 * (2 - t) - 2 * (-1)) / (2 - t) ^ 2 / (2 / (2 - t)) = 1 / (2 - t) := by
    field_simp
    ring
  rw [hderiv] at hlog
  exact hlog

/-- On `[0, 1]` the burn obeys the reduced variable-mass law `m v' = -ve * m'` with exhaust speed
`ve = 1` and `m' = -1`, and the common value, the thrust `ve * (-m')`, is `1`. -/
lemma burn_law {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    burnMass t * (1 / (2 - t)) = -1 * (-1) ∧ burnMass t * (1 / (2 - t)) = 1 := by
  have hne : (2 : ℝ) - t ≠ 0 := by
    have h := burnMass_pos ht
    unfold burnMass at h
    exact ne_of_gt h
  have h : (2 - t) * (1 / (2 - t)) = 1 := by field_simp
  have h' : burnMass t * (1 / (2 - t)) = 1 := h
  exact ⟨by rw [h']; norm_num, h'⟩

/-! ## H. Velocity and position histories -/

/-- The burn starts from rest at the origin: `x 0 = 0` and `v 0 = 0`. -/
lemma burn_initial : burnPosition 0 = 0 ∧ burnVelocity 0 = 0 := by
  have h1 : ((2 : ℝ) - 0) / 2 = 1 := by norm_num
  have h2 : (2 : ℝ) / ((2 : ℝ) - 0) = 1 := by norm_num
  constructor
  · unfold burnPosition
    rw [h1, Real.log_one, mul_zero, add_zero]
  · unfold burnVelocity
    rw [h2, Real.log_one]

/-- Before depletion (`t < 2`) the position has derivative `x' = v`. -/
lemma hasDerivAt_burnPosition {t : ℝ} (ht : t < 2) :
    HasDerivAt burnPosition (burnVelocity t) t := by
  have hpos : (0 : ℝ) < 2 - t := by linarith
  have h2t : (2 : ℝ) - t ≠ 0 := ne_of_gt hpos
  have hg_ne : ((2 : ℝ) - t) / 2 ≠ 0 := div_ne_zero h2t (by norm_num)
  have hden : HasDerivAt (fun x : ℝ => (2 : ℝ) - x) (-1) t := hasDerivAt_burnMass t
  have hg : HasDerivAt (fun x : ℝ => ((2 : ℝ) - x) / 2) (-1 / 2) t :=
    hden.div_const 2
  have hlogg : HasDerivAt (fun x : ℝ => Real.log (((2 : ℝ) - x) / 2))
      ((-1 / 2) / (((2 : ℝ) - t) / 2)) t :=
    hg.log hg_ne
  have hmul : HasDerivAt (fun x : ℝ => ((2 : ℝ) - x) * Real.log (((2 : ℝ) - x) / 2))
      (-1 * Real.log (((2 : ℝ) - t) / 2) + (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2))) t :=
    hden.fun_mul hlogg
  have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have hadd : HasDerivAt (fun x : ℝ => x + ((2 : ℝ) - x) * Real.log (((2 : ℝ) - x) / 2))
      (1 + (-1 * Real.log (((2 : ℝ) - t) / 2) + (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2)))) t :=
    hid.fun_add hmul
  have hmul_eq : (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2)) = -1 := by
    field_simp
  have hlog_eq : Real.log (2 / (2 - t)) = -Real.log (((2 : ℝ) - t) / 2) := by
    have hinv : (2 : ℝ) / (2 - t) = (((2 : ℝ) - t) / 2)⁻¹ := (inv_div _ _).symm
    rw [hinv, Real.log_inv]
  have hderiv : 1 + (-1 * Real.log (((2 : ℝ) - t) / 2) + (2 - t) * ((-1 / 2) / (((2 : ℝ) - t) / 2)))
      = Real.log (2 / (2 - t)) := by
    rw [hmul_eq, hlog_eq]
    ring
  rw [hderiv] at hadd
  exact hadd

/-- The ideal rocket equation `velocity_increment_eq_log` for this burn: the velocity gained on
`[0, 1]` is `ve * log (m 0 / m 1)` with `ve = 1`. -/
lemma burnVelocity_increment :
    burnVelocity 1 - burnVelocity 0 = 1 * Real.log (burnMass 0 / burnMass 1) := by
  have htb : (0 : ℝ) ≤ 1 := by norm_num
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt burnMass (-1) t :=
    fun t _ => hasDerivAt_burnMass t
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt burnVelocity (1 / (2 - t)) t := by
    intro t ht
    rw [mem_Icc] at ht
    exact hasDerivAt_burnVelocity (by linarith)
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < burnMass t := fun t ht => burnMass_pos ht
  have hlaw : ∀ t ∈ Icc (0 : ℝ) 1, burnMass t * (1 / (2 - t)) = -1 * (-1) := by
    intro t ht
    exact (burn_law ht).1
  exact velocity_increment_eq_log (m := burnMass) (v := burnVelocity)
    (m' := fun _ => (-1 : ℝ)) (v' := fun t => 1 / (2 - t)) (ve := (1 : ℝ)) (tb := (1 : ℝ))
    htb hm hv hpos hlaw

/-- The displacement over the burn is the integral of the velocity: `x 1 - x 0 = ∫₀¹ v`. -/
lemma burnPosition_sub_eq_integral :
    burnPosition 1 - burnPosition 0 = ∫ t in (0 : ℝ)..1, burnVelocity t := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt burnPosition (burnVelocity x) x := by
    rw [uIcc_of_le h01]
    intro x hx
    rw [mem_Icc] at hx
    exact hasDerivAt_burnPosition (by linarith)
  have hcont : ContinuousOn burnVelocity (Icc (0 : ℝ) 1) := by
    intro x hx
    rw [mem_Icc] at hx
    exact (hasDerivAt_burnVelocity (by linarith : x < 2)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable burnVelocity MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc h01 hcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  exact hFTC.symm

/-! ## I. The target and the rendezvous -/

/-- The target coasts at the constant speed `log 2`. -/
lemma hasDerivAt_targetPosition (t : ℝ) : HasDerivAt targetPosition (Real.log 2) t := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ) - 2 * Real.log 2) 0 t :=
    hasDerivAt_const t _
  have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have hmul : HasDerivAt (fun x : ℝ => x * Real.log 2) (1 * Real.log 2) t :=
    hid.mul_const (Real.log 2)
  have hadd : HasDerivAt (fun i : ℝ => (1 - 2 * Real.log 2) + i * Real.log 2)
      (0 + 1 * Real.log 2) t :=
    hconst.fun_add hmul
  have hderiv : (0 : ℝ) + 1 * Real.log 2 = Real.log 2 := by ring
  rw [hderiv] at hadd
  exact hadd

/-- Rendezvous at `t = 1`: the positions agree, the burn's velocity is the target's speed
`log 2`, both positions have derivative `log 2` at `t = 1`, and the mass stays positive on the
burn interval. -/
lemma rendezvous :
    burnPosition 1 = targetPosition 1 ∧ burnVelocity 1 = Real.log 2 ∧
      HasDerivAt burnPosition (Real.log 2) 1 ∧ HasDerivAt targetPosition (Real.log 2) 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, 0 < burnMass t := by
  have h21 : ((2 : ℝ) - 1) / 2 = 1 / 2 := by norm_num
  have h2t1 : (2 : ℝ) / ((2 : ℝ) - 1) = 2 := by norm_num
  have hlog_half : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    have h : ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ := by norm_num
    rw [h, Real.log_inv]
  have hv1 : burnVelocity 1 = Real.log 2 := by
    unfold burnVelocity
    rw [h2t1]
  have hx1 : burnPosition 1 = 1 - Real.log 2 := by
    unfold burnPosition
    rw [h21, hlog_half]
    ring
  have ht1 : targetPosition 1 = 1 - Real.log 2 := by
    unfold targetPosition
    ring
  have hpos1 : burnPosition 1 = targetPosition 1 := by rw [hx1, ht1]
  have hderiv : HasDerivAt burnPosition (Real.log 2) 1 := by
    have h := hasDerivAt_burnPosition (show (1 : ℝ) < 2 by norm_num)
    rw [hv1] at h
    exact h
  exact ⟨hpos1, hv1, hderiv, hasDerivAt_targetPosition 1, fun t ht => burnMass_pos ht⟩

end PhyslibExt.Mechanics.SpaceTrajectoryModels
