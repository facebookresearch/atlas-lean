/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.CrossProduct
public import PhyslibExt.EarthScience.KeplerThirdLaw
public import PhyslibExt.Units.EngineeringFrames

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.LinearAlgebra.CrossProduct

/-!
# Orbital ports: vis-viva, impulses, circular orbits and the eccentricity vector

## i. Overview

A state of relative two-body motion is a position `x` and a velocity `v` in `Fin 3 → ℝ`,
relative to the attracting center at the origin of a fixed inertial frame, with gravitational
parameter `μ = G (m₁ + m₂) > 0`. Its specific energy is `E = |v|² / 2 - μ / r`, `r = |x|`, and
for `E < 0` the energy-defined semi-major axis is `a = -μ / (2 E)`. Then `a > 0`, and for a
collision-free state (`r > 0`) the vis-viva identity `|v|² = μ (2 / r - 1 / a)` holds.

A state at circular speed has `|v|² = μ / r`; it has `E = -μ / (2 r)` and `a = r` whatever the
direction of `v`. A circular state also has its velocity transverse to its position,
`x ⬝ᵥ v = 0`, and then its specific angular momentum satisfies `|x ⨯₃ v|² = μ r`; a radial
state at circular speed has `x ⨯₃ v = 0`.

The Euclidean squares are dot products, `|v|² = v ⬝ᵥ v`: the default norm on `Fin 3 → ℝ` is the
sup norm and is not used. The specific angular momentum, the angular momentum per unit reduced
mass, is the cross product `x ⨯₃ v`.

A tangential impulse of signed magnitude `Δv` changes the velocity along the flight direction,
`v' = v + (Δv / |v|) • v`, at the fixed position: the squared speed becomes `(|v| + Δv)²`, the
specific angular momentum is multiplied by `1 + Δv / |v|`, and vis-viva applied to the new
state gives the new semi-major axis. The specific angular momentum identity alone gives no
orbital plane: there is none when `x ⨯₃ v = 0`, and none after an impulse with `Δv = -|v|`,
which brings the body to rest.

Sections A and B give identities about one fixed state, not about a trajectory. No solution of the
two-body equation is constructed, no elliptic trajectory is asserted (a state with `E < 0` and
zero specific angular momentum is radial), and no transfer cost or two-impulse optimality is
claimed. At `E = 0` the formula `-μ / (2 E)` returns Lean's junk value `0`, not a finite
semi-major axis.

A circular orbit is taken in the form of the circular-orbit lemmas of Physlib's
`PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Circular`: a planar position
`r t` and velocity `v t`, complex numbers whose real and imaginary parts are the coordinates
along two in-plane axes, relative to the center, with gravitational parameter `μ > 0` and radius
`R > 0`, such that `‖r t‖ = R`, `r' = v` and `v' = -(μ / ‖r t‖ ^ 3) • r t` for all `t`
(`IsCircularOrbit`). These are premises: this module constructs no circular trajectory and
proves no circular dynamics, and the premises do not follow from the speed balance
`v ^ 2 = μ / R` alone. That Physlib module is not part of the Physlib version this repository
depends on, so its circular position and velocity do not yet discharge the premises here; that
discharge waits for a Physlib update.

From the premises the circular balance `‖v‖ ^ 2 = μ / R` is derived, and the existing
circular-speed algebra (`EarthScience.kepler_circular_speed`, `EarthScience.kepler_third_law`)
gives the speed `√(μ / R)` and the period `2 π R / ‖v‖` with `T ^ 2 = 4 π ^ 2 R ^ 3 / μ`.
Engineering units map onto the premises: with `l, s > 0` new length and time units per old
unit, lengths scale by `l`, times by `s`, speeds by `l / s` and the gravitational parameter by
`l ^ 3 / s ^ 2`; a time-unit change without the factor `s⁻²` on `μ` is rejected, and so is the
collision radius `R = 0`. The planar state maps to inertial components by the passive frame map
`Q (x, y, 0)`, `Q ∈ SO(3)`, of `Units.EngineeringFrames.bodyToInertialVec`: the spatial state
keeps the distance `R`, the velocity and the inverse-square attraction, and stays in the plane
normal to `Q e₃`.

Sections G to I are algebra at one state again, stated without an angle chart. The eccentricity
vector is `e = (v ⨯₃ h) / μ - x / r` with `h = x ⨯₃ v`, and `|e|² = 1 + 2 E |h|² / μ²` for
`μ > 0` and `r > 0`; a bound state, `E < 0`, with `h ≠ 0` has `0 ≤ |e| < 1` and `a > 0`. The
classical angles are charts that fail where their defining vectors vanish: the pericenter
direction `e / |e|` is undefined exactly for circular states (`e = 0` iff `x ⬝ᵥ v = 0` and
`|v|² = μ / r`), and the ascending-node direction `n = k ⨯₃ h`, with `k = (0, 0, 1)` the pole of
the reference plane, is undefined exactly when `h` lies along the pole. A radial state (`h = 0`)
has `|e| = 1` whatever its energy, so `h ≠ 0` cannot be dropped from the bound. A proper rotation
of the state rotates `e` and keeps `|e|`. No conservation of `e` or `a` and no conic trajectory is
asserted.

Sections J to L embed a planar Kepler coast in the oriented plane of an orbit-plane frame. The
coast is taken in the form of the comparison arcs of Physlib's
`PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.KeplerConservation`: real
coordinate functions `x, y, vx, vy` of time on a positive finite interval `[t₀, t₁]`, with no
collision (`√(x² + y²) > 0`), position derivatives the velocity components and velocity
derivatives the Newtonian central acceleration `-μ (x, y) / √(x² + y²)³`, for a gravitational
parameter `μ > 0` (`IsPlanarKeplerArc`). The Physlib arcs take any real `μ`; here `μ = 0`, which
admits a body at rest, and a repulsive `μ < 0` are excluded. These are premises: this module
constructs no trajectory and proves no planar conservation law.
That Physlib module states the conservation of its planar energy `vx² + vy² - 2 μ / √(x² + y²)`,
twice the specific energy, and of its signed angular momentum `x vy - y vx` as equalities of their
values at `t₀` and `t₁`; here those two endpoint equalities are hypotheses, in that
normalization. That Physlib module is not part of the Physlib version this repository depends on.

The planar state embeds by the passive frame map `Q (x, y, 0)` of `spatialState`, `Q ∈ SO(3)`:
the plane is spanned by `Q e₁` and `Q e₂`, and its oriented normal is `Q e₃ = Q e₁ ⨯₃ Q e₂`. The
embedded arc stays away from the center, its position has derivative its velocity, and its
velocity has derivative the inverse-square attraction `-(μ / |X| ^ 3) X`. The planar energy is
twice the specific energy `|V|² / 2 - μ / |X|` of the spatial state, so the factor two of that
normalization stays explicit. The specific angular momentum `X ⨯₃ V` is the planar signed angular
momentum times `Q e₃`, so its component along the oriented normal is the planar value; an
orthogonal map of determinant `-1` reverses that component.

Section M gives the cost of one equal-speed plane change at a node: two velocities `v₁` and `v₂`
tangent at the node `x` (`x ⬝ᵥ vₖ = 0`), with the same speed `v > 0` and specific angular
momenta `x ⨯₃ vₖ` at the angle `i ∈ [0, π]`, differ by a single impulse of magnitude
`|v₂ - v₁| = 2 v sin(i / 2)`. This is the magnitude of that one specified impulse, not of an
optimized transfer.

Each result assumes only the hypotheses its proof uses.

## ii. Key results

- `OrbitalPorts.visViva`: `|v|² = μ (2 / r - 1 / a)` for `μ, r > 0`, `E < 0`.
- `OrbitalPorts.semiMajorAxis_pos`: `a > 0` follows from `μ > 0`, `E < 0`.
- `OrbitalPorts.visViva_tangentialImpulse`: the identity after one tangential impulse.
- `OrbitalPorts.semiMajorAxis_of_circularSpeed`, `OrbitalPorts.semiMajorAxis_of_circular`:
  circular speed gives `a = r`; a circular state also has `|x ⨯₃ v|² = μ r`.
- `OrbitalPorts.semiMajorAxis_tangentialImpulse_eq_radius_iff`: at circular speed, one impulse
  keeps `a = r` only if it keeps the speed or reverses the velocity.
- `OrbitalPorts.IsCircularOrbit`: the circular-orbit premises.
- `OrbitalPorts.IsCircularOrbit.norm_vel_eq`, `OrbitalPorts.IsCircularOrbit.period_sq`: speed
  `√(μ / R)` and Kepler's third law.
- `OrbitalPorts.IsCircularOrbit.unitChange`, `OrbitalPorts.IsCircularOrbit.not_wrong_time_unit`,
  `OrbitalPorts.not_isCircularOrbit_zero_radius`: units, and the two rejected inputs.
- `OrbitalPorts.IsCircularOrbit.hasDerivAt_spatialVelocity`: the inverse-square law in inertial
  components.
- `OrbitalPorts.eccentricity_sq`, `OrbitalPorts.eccentricity_lt_one_and_semiMajorAxis_pos`: the
  energy identity `|e|² = 1 + 2 E |h|² / μ²` and, for a bound state with `h ≠ 0`, `0 ≤ |e| < 1`
  and `a > 0`.
- `OrbitalPorts.eccentricityVector_eq_zero_iff`, `OrbitalPorts.nodeVector_eq_zero_iff`,
  `OrbitalPorts.eccentricityVector_of_cross_eq_zero`: where the pericenter and node directions
  are undefined, and the radial boundary `|e| = 1`.
- `OrbitalPorts.eccentricityVector_mulVec`: frame covariance under proper rotations.
- `OrbitalPorts.IsPlanarKeplerArc`: the planar Kepler arc premises, with `μ > 0`.
- `OrbitalPorts.two_mul_specificEnergy_spatialState`,
  `OrbitalPorts.specificEnergy_spatialState_eq_of_energy_eq`: the planar energy is twice the
  spatial specific energy, and equal planar energies give equal specific energies.
- `OrbitalPorts.cross_spatialState`, `OrbitalPorts.cross_spatialState_dotProduct_normal`,
  `OrbitalPorts.cross_spatialState_eq_of_angular_eq`: the specific angular momentum along the
  oriented normal.
- `OrbitalPorts.cross_dotProduct_normal_of_det_eq_neg_one`: a reflection reverses the signed
  component.
- `OrbitalPorts.IsPlanarKeplerArc.hasDerivAt_spatialVelocity`: the inverse-square law for the
  embedded arc.
- `OrbitalPorts.impulseMagnitude_planeChange`: one equal-speed plane change by the angle `i`
  costs `2 v sin(i / 2)`.

## iii. Table of contents

- A. State energy and vis-viva
- B. One tangential impulse
- C. The circular-orbit premises
- D. Speed and period
- E. Units
- F. Planar to spatial state
- G. The eccentricity vector and the energy identity
- H. Undefined pericenter and node directions
- I. Frame covariance
- J. The planar Kepler arc premises
- K. Energy and angular momentum in the spatial plane
- L. The spatial Kepler arc
- M. One equal-speed plane change

## iv. References

- H. D. Curtis, *Orbital Mechanics for Engineering Students*, ch. 2: specific energy,
  `a = -μ / (2 ε)`, the vis-viva equation and circular orbits (`v = √(μ / r)`,
  `T = 2 π r ^ (3 / 2) / √μ`), and the eccentricity vector with `e² = 1 + 2 ε h² / μ²`; ch. 4:
  the node line `N = K × h`; ch. 6: the simple plane change `Δv = 2 v sin(δ / 2)`.
- R. R. Bate, D. D. Mueller and J. E. White, *Fundamentals of Astrodynamics*, ch. 1-2.
- D. A. Vallado, *Fundamentals of Astrodynamics and Applications*, ch. 1-2: the two-body
  equation `r'' = -μ r / r ^ 3`, the orbital plane, and the special cases of the classical
  elements (circular and equatorial orbits); ch. 6: inclination-only changes.
- Physlib, `PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Circular`: the
  circular orbits whose conclusions are the premises of section C.
- Physlib, `PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.KeplerConservation`:
  the planar comparison arcs whose fields are the premises of section J, and the planar energy and
  signed angular momentum whose endpoint equalities are the hypotheses of section K.
- `crossProduct` and `dotProduct` in Mathlib.

## A. State energy and vis-viva
-/

@[expose] public section

namespace OrbitalPorts

open Matrix

/-- Squared Euclidean speed `|v|² = v ⬝ᵥ v`. -/
def speedSq (v : Fin 3 → ℝ) : ℝ := v ⬝ᵥ v

/-- Euclidean distance `r = √(x ⬝ᵥ x)` from the attracting center at the origin. -/
noncomputable def radius (x : Fin 3 → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ x)

/-- Specific energy `E = |v|² / 2 - μ / r` of the state `(x, v)`. At the collision point `x = 0`
Lean's convention `μ / 0 = 0` gives a meaningless value. -/
noncomputable def specificEnergy (μ : ℝ) (x v : Fin 3 → ℝ) : ℝ :=
  speedSq v / 2 - μ / radius x

/-- Energy-defined semi-major axis `a = -μ / (2 E)`. It is a length only for `E < 0`; at `E = 0`
(parabolic) Lean's convention `x / 0 = 0` gives the meaningless value `0`. -/
noncomputable def semiMajorAxis (μ : ℝ) (x v : Fin 3 → ℝ) : ℝ :=
  -μ / (2 * specificEnergy μ x v)

/-- `a > 0` follows from `μ > 0` and `E < 0`. -/
lemma semiMajorAxis_pos {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ)
    (hE : specificEnergy μ x v < 0) : 0 < semiMajorAxis μ x v := by
  unfold semiMajorAxis
  apply div_pos_of_neg_of_neg
  · exact neg_lt_zero.mpr hμ
  · exact mul_neg_of_pos_of_neg two_pos hE

/-- Energy-defined vis-viva: for a collision-free state (`r > 0`) with `μ > 0` and `E < 0`,
`|v|² = μ (2 / r - 1 / a)`. -/
lemma visViva {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ) (hr : 0 < radius x)
    (hE : specificEnergy μ x v < 0) :
    speedSq v = μ * (2 / radius x - 1 / semiMajorAxis μ x v) := by
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hr0 : radius x ≠ 0 := ne_of_gt hr
  have hE0 : specificEnergy μ x v ≠ 0 := ne_of_lt hE
  have ha0 : semiMajorAxis μ x v ≠ 0 := ne_of_gt (semiMajorAxis_pos hμ hE)
  unfold semiMajorAxis specificEnergy
  field_simp
  ring

/-- A parabolic state (`E = 0`) has no finite semi-major axis: `-μ / (2 E)` is the junk value
`0`, so `a > 0` fails and `E < 0` cannot be weakened to `E ≤ 0`. -/
lemma semiMajorAxis_of_specificEnergy_eq_zero {μ : ℝ} {x v : Fin 3 → ℝ}
    (hE : specificEnergy μ x v = 0) :
    semiMajorAxis μ x v = 0 ∧ ¬ 0 < semiMajorAxis μ x v := by
  have h : semiMajorAxis μ x v = 0 := by
    unfold semiMajorAxis
    rw [hE, mul_zero, div_zero]
  exact ⟨h, by rw [h]; exact lt_irrefl 0⟩

/-- A state at circular speed, `|v|² = μ / r` with `μ, r > 0`, has `E = -μ / (2 r)` and
`a = r`. The speed does not fix the direction: a radial state at this speed has the same `E`
and `a`. `semiMajorAxis_of_circular` adds the transverse condition of a circular state. -/
lemma semiMajorAxis_of_circularSpeed {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ) (hr : 0 < radius x)
    (hv : speedSq v = μ / radius x) :
    specificEnergy μ x v = -μ / (2 * radius x) ∧ semiMajorAxis μ x v = radius x := by
  have hr0 : radius x ≠ 0 := ne_of_gt hr
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hE : specificEnergy μ x v = -μ / (2 * radius x) := by
    unfold specificEnergy
    rw [hv]
    field_simp
    ring
  refine ⟨hE, ?_⟩
  unfold semiMajorAxis
  rw [hE]
  field_simp

/-- A circular state: circular speed `|v|² = μ / r` and a velocity transverse to the position,
`x ⬝ᵥ v = 0`, with `μ, r > 0`. It has `E = -μ / (2 r)`, `a = r` and the circular specific
angular momentum `|x ⨯₃ v|² = μ r`. -/
lemma semiMajorAxis_of_circular {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ) (hr : 0 < radius x)
    (hv : speedSq v = μ / radius x) (hperp : x ⬝ᵥ v = 0) :
    specificEnergy μ x v = -μ / (2 * radius x) ∧ semiMajorAxis μ x v = radius x ∧
      (x ⨯₃ v) ⬝ᵥ (x ⨯₃ v) = μ * radius x := by
  obtain ⟨hE, ha⟩ := semiMajorAxis_of_circularSpeed hμ hr hv
  refine ⟨hE, ha, ?_⟩
  have hxx : x ⬝ᵥ x = radius x ^ 2 := by
    unfold radius
    rw [Real.sq_sqrt]
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hvx : v ⬝ᵥ x = 0 := by
    rw [dotProduct_comm]
    exact hperp
  have hr0 : radius x ≠ 0 := ne_of_gt hr
  unfold speedSq at hv
  rw [cross_dot_cross, hperp, hvx, hxx, hv]
  field_simp
  ring

/-! ## B. One tangential impulse -/

/-- Velocity after a tangential impulse of signed magnitude `Δv` along the flight direction:
`v' = v + (Δv / |v|) • v`, at an unchanged position. Declared for `v ≠ 0`; at `v = 0` the
direction is undefined and the formula returns `v`. -/
noncomputable def tangentialImpulse (v : Fin 3 → ℝ) (Δv : ℝ) : Fin 3 → ℝ :=
  v + (Δv / Real.sqrt (speedSq v)) • v

/-- Post-impulse speed: `|v'|² = (|v| + Δv)²` for `v ≠ 0`. -/
lemma speedSq_tangentialImpulse {v : Fin 3 → ℝ} (hv : v ≠ 0) (Δv : ℝ) :
    speedSq (tangentialImpulse v Δv) = (Real.sqrt (speedSq v) + Δv) ^ 2 := by
  have hs_nonneg : 0 ≤ speedSq v := by
    unfold speedSq dotProduct
    apply Finset.sum_nonneg
    intro i _
    exact mul_self_nonneg _
  have hs_ne : speedSq v ≠ 0 := by
    unfold speedSq
    intro h0
    exact hv (dotProduct_self_eq_zero.mp h0)
  have hs_pos : 0 < speedSq v := lt_of_le_of_ne hs_nonneg (Ne.symm hs_ne)
  have ht_pos : 0 < Real.sqrt (speedSq v) := Real.sqrt_pos.mpr hs_pos
  have ht_ne : Real.sqrt (speedSq v) ≠ 0 := ne_of_gt ht_pos
  have hsq : Real.sqrt (speedSq v) ^ 2 = speedSq v := Real.sq_sqrt hs_nonneg
  unfold speedSq at hsq ht_ne
  unfold tangentialImpulse speedSq
  rw [add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp
  linear_combination (-(Real.sqrt (v ⬝ᵥ v) + Δv) ^ 2) * hsq

/-- A tangential impulse multiplies the specific angular momentum `x ⨯₃ v` by `1 + Δv / |v|`.
The identity holds for all `x`, `v` and `Δv` and by itself gives no orbital plane: there is none
when `x ⨯₃ v = 0` (a radial state, or `v = 0`) or when the factor vanishes (`Δv = -|v|` brings
the body to rest). When both are nonzero, the new specific angular momentum is a nonzero
multiple of the old one. -/
lemma cross_tangentialImpulse (x v : Fin 3 → ℝ) (Δv : ℝ) :
    x ⨯₃ tangentialImpulse v Δv = (1 + Δv / Real.sqrt (speedSq v)) • (x ⨯₃ v) := by
  unfold tangentialImpulse
  rw [map_add, map_smul]
  nth_rewrite 1 [← one_smul ℝ (x ⨯₃ v)]
  rw [← add_smul]

/-- Vis-viva after one tangential impulse at the fixed state: if the post-impulse energy is
negative, `(|v| + Δv)² = μ (2 / r - 1 / a')` for the post-impulse semi-major axis `a'`, that is
`1 / a' = 2 / r - (|v| + Δv)² / μ`. -/
lemma visViva_tangentialImpulse {μ Δv : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ) (hr : 0 < radius x)
    (hv : v ≠ 0) (hE : specificEnergy μ x (tangentialImpulse v Δv) < 0) :
    (Real.sqrt (speedSq v) + Δv) ^ 2
        = μ * (2 / radius x - 1 / semiMajorAxis μ x (tangentialImpulse v Δv)) ∧
      1 / semiMajorAxis μ x (tangentialImpulse v Δv)
        = 2 / radius x - (Real.sqrt (speedSq v) + Δv) ^ 2 / μ := by
  have hvv := visViva hμ hr hE
  rw [speedSq_tangentialImpulse hv Δv] at hvv
  refine ⟨hvv, ?_⟩
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hr0 : radius x ≠ 0 := ne_of_gt hr
  have ha0 : semiMajorAxis μ x (tangentialImpulse v Δv) ≠ 0 :=
    ne_of_gt (semiMajorAxis_pos hμ hE)
  field_simp at hvv ⊢
  linear_combination hvv

/-- At circular speed, `|v|² = μ / r`, a tangential impulse with negative post-impulse energy
keeps `a' = r` only if it keeps the speed (`Δv = 0`) or reverses the velocity
(`Δv = -2 |v|`). Only the speed enters: the statement holds for a circular state
(`semiMajorAxis_of_circular`) and for a radial state at circular speed alike. No transfer
cost or optimality is claimed. -/
lemma semiMajorAxis_tangentialImpulse_eq_radius_iff {μ Δv : ℝ} {x v : Fin 3 → ℝ}
    (hμ : 0 < μ) (hr : 0 < radius x) (hspeed : speedSq v = μ / radius x)
    (hE : specificEnergy μ x (tangentialImpulse v Δv) < 0) :
    semiMajorAxis μ x (tangentialImpulse v Δv) = radius x ↔
      Δv = 0 ∨ Δv = -2 * Real.sqrt (speedSq v) := by
  have hs_pos : 0 < speedSq v := by rw [hspeed]; exact div_pos hμ hr
  have hv0 : v ≠ 0 := by
    intro h0
    have hs0 : speedSq v = 0 := by
      unfold speedSq
      exact dotProduct_self_eq_zero.mpr h0
    rw [hs0] at hs_pos
    exact lt_irrefl 0 hs_pos
  have hs_nonneg : 0 ≤ speedSq v := by
    unfold speedSq dotProduct
    apply Finset.sum_nonneg
    intro i _
    exact mul_self_nonneg _
  have hsq : Real.sqrt (speedSq v) ^ 2 = speedSq v := Real.sq_sqrt hs_nonneg
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hr0 : radius x ≠ 0 := ne_of_gt hr
  have ha0 : semiMajorAxis μ x (tangentialImpulse v Δv) ≠ 0 :=
    ne_of_gt (semiMajorAxis_pos hμ hE)
  obtain ⟨h1, h2⟩ := visViva_tangentialImpulse hμ hr hv0 hE
  constructor
  · intro ha
    rw [ha] at h2
    have hS_eq : (Real.sqrt (speedSq v) + Δv) ^ 2 = μ / radius x := by
      field_simp at h2 ⊢
      linear_combination h2
    have ht2 : (Real.sqrt (speedSq v) + Δv) ^ 2 = Real.sqrt (speedSq v) ^ 2 := by
      rw [hS_eq, ← hspeed, hsq]
    have hfac : Δv * (Δv + 2 * Real.sqrt (speedSq v)) = 0 := by
      linear_combination ht2
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact Or.inl h0
    · right
      linarith
  · intro hdisj
    have ht2 : (Real.sqrt (speedSq v) + Δv) ^ 2 = Real.sqrt (speedSq v) ^ 2 := by
      rcases hdisj with h0 | h0
      · rw [h0]
        ring
      · rw [h0]
        ring
    have hS_eq : (Real.sqrt (speedSq v) + Δv) ^ 2 = μ / radius x := by
      rw [ht2, hsq, hspeed]
    rw [hS_eq] at h2
    have hdiv : 1 / semiMajorAxis μ x (tangentialImpulse v Δv) = 1 / radius x := by
      field_simp at h2 ⊢
      linear_combination h2
    field_simp at hdiv
    exact hdiv.symm

open EarthScience (kepler_circular_speed kepler_third_law)
open Units.EngineeringFrames (bodyToInertialVec bodyToInertialVec_dotProduct)

/-! ## C. The circular-orbit premises -/

/-- Circular-orbit premises for a planar position `r` and velocity `v` relative to the attracting
center (complex numbers: real part along the first in-plane axis, imaginary part along the
second), gravitational parameter `μ` and radius `R`. They are the conclusions of the upstream
circular-orbit lemmas, taken as premises. -/
structure IsCircularOrbit (μ R : ℝ) (r v : ℝ → ℂ) : Prop where
  /-- The gravitational parameter is positive. -/
  mu_pos : 0 < μ
  /-- The radius is positive: the collision orbit `R = 0` is excluded. -/
  radius_pos : 0 < R
  /-- The position stays on the circle of radius `R` about the center. -/
  norm_eq : ∀ t, ‖r t‖ = R
  /-- The velocity is the time derivative of the position. -/
  hasDerivAt_pos : ∀ t, HasDerivAt r (v t) t
  /-- The acceleration is the inverse-square attraction toward the center. -/
  hasDerivAt_vel : ∀ t, HasDerivAt v (-(μ / ‖r t‖ ^ 3) • r t) t

/-- Collision radius zero is rejected: no circular orbit has radius `0`. -/
lemma not_isCircularOrbit_zero_radius (μ : ℝ) (r v : ℝ → ℂ) : ¬ IsCircularOrbit μ 0 r v := by
  intro h
  exact absurd h.radius_pos (lt_irrefl 0)

/-! ## D. Speed and period -/

/-- The circular balance `‖v‖ ^ 2 = μ / R`, derived from the premises. -/
lemma IsCircularOrbit.norm_vel_sq {μ R : ℝ} {r v : ℝ → ℂ} (h : IsCircularOrbit μ R r v)
    (t : ℝ) : ‖v t‖ ^ 2 = μ / R := by
  have hnorm : ∀ u, inner ℂ (r u) (r u) = ((R ^ 2 : ℝ) : ℂ) := by
    intro u
    rw [inner_self_eq_norm_sq_to_K, h.norm_eq u]
    norm_cast
  have hconst1 : ∀ u, HasDerivAt (fun u => inner ℂ (r u) (r u)) 0 u := by
    intro u
    have heq : (fun u => inner ℂ (r u) (r u)) = fun _ => ((R ^ 2 : ℝ) : ℂ) :=
      funext hnorm
    rw [heq]
    exact hasDerivAt_const u _
  have hort : ∀ u, inner ℂ (r u) (v u) + inner ℂ (v u) (r u) = 0 := fun u =>
    (HasDerivAt.inner ℂ (h.hasDerivAt_pos u) (h.hasDerivAt_pos u)).unique (hconst1 u)
  have hre : ∀ u, RCLike.re (inner ℂ (r u) (v u)) = 0 := by
    intro u
    have h2 := congrArg RCLike.re (hort u)
    rw [map_add, map_zero, inner_re_symm] at h2
    rw [inner_re_symm]
    linarith
  have hderiv2 : HasDerivAt (fun u => inner ℂ (r u) (v u))
      (inner ℂ (r t) (-(μ / ‖r t‖ ^ 3) • r t) + inner ℂ (v t) (v t)) t :=
    HasDerivAt.inner ℂ (h.hasDerivAt_pos t) (h.hasDerivAt_vel t)
  have hderiv2re : HasDerivAt (⇑RCLike.reCLM ∘ (fun u => inner ℂ (r u) (v u)))
      (RCLike.reCLM (inner ℂ (r t) (-(μ / ‖r t‖ ^ 3) • r t) + inner ℂ (v t) (v t))) t :=
    HasFDerivAt.comp_hasDerivAt t (ContinuousLinearMap.hasFDerivAt RCLike.reCLM) hderiv2
  have hconst2 : HasDerivAt (⇑RCLike.reCLM ∘ (fun u => inner ℂ (r u) (v u))) 0 t := by
    have heq : ⇑RCLike.reCLM ∘ (fun u => inner ℂ (r u) (v u)) = fun _ => (0 : ℝ) := by
      funext u
      simp only [Function.comp_apply, RCLike.reCLM_apply]
      exact hre u
    rw [heq]
    exact hasDerivAt_const t _
  have hsum := hderiv2re.unique hconst2
  rw [map_add] at hsum
  have hvself : RCLike.reCLM (inner ℂ (v t) (v t)) = ‖v t‖ ^ 2 := by
    have hs := inner_self_eq_norm_sq (𝕜 := ℂ) (v t)
    rwa [RCLike.reCLM_apply]
  have hrv : RCLike.reCLM (inner ℂ (r t) (-(μ / ‖r t‖ ^ 3) • r t)) = -(μ / R) := by
    have hsmul : (-(μ / ‖r t‖ ^ 3) : ℝ) • r t
        = ((-(μ / ‖r t‖ ^ 3) : ℝ) : ℂ) • r t :=
      RCLike.real_smul_eq_coe_smul _ _
    rw [hsmul, inner_smul_right, hnorm t, ← Complex.ofReal_mul]
    have hoR : ∀ x : ℝ, RCLike.reCLM ((x : ℝ) : ℂ) = x := fun x => by
      rw [RCLike.reCLM_apply]
      exact RCLike.ofReal_re x
    rw [hoR, h.norm_eq t]
    have hRne : R ≠ 0 := ne_of_gt h.radius_pos
    field_simp
  rw [hrv, hvself] at hsum
  linarith

/-- The speed is the circular speed `√(μ / R)` of the existing algebra (`kepler_circular_speed`
with `G = μ`, `M = 1`). -/
lemma IsCircularOrbit.norm_vel_eq {μ R : ℝ} {r v : ℝ → ℂ} (h : IsCircularOrbit μ R r v)
    (t : ℝ) : ‖v t‖ = Real.sqrt (μ / R) := by
  have hsq := h.norm_vel_sq t
  have hpos : 0 < μ / R := div_pos h.mu_pos h.radius_pos
  have hne : ‖v t‖ ≠ 0 := by
    intro hz
    rw [hz, zero_pow two_ne_zero] at hsq
    linarith
  have hv : 0 < ‖v t‖ := lt_of_le_of_ne (norm_nonneg _) hne.symm
  have hbal : ‖v t‖ ^ 2 = μ * 1 / R := by
    rw [hsq, mul_one]
  have hcs := kepler_circular_speed h.mu_pos one_pos h.radius_pos hv hbal
  rwa [mul_one] at hcs

/-- The period `T = 2 π R / ‖v‖`, the time to travel the circumference at the constant speed,
satisfies Kepler's third law `T ^ 2 = 4 π ^ 2 R ^ 3 / μ` (`kepler_third_law`). -/
lemma IsCircularOrbit.period_sq {μ R : ℝ} {r v : ℝ → ℂ} (h : IsCircularOrbit μ R r v) (t : ℝ) :
    (2 * Real.pi * R / ‖v t‖) ^ 2 = 4 * Real.pi ^ 2 * R ^ 3 / μ := by
  have hsq := h.norm_vel_sq t
  have hpos : 0 < μ / R := div_pos h.mu_pos h.radius_pos
  have hne : ‖v t‖ ≠ 0 := by
    intro hz
    rw [hz, zero_pow two_ne_zero] at hsq
    linarith
  have hv : 0 < ‖v t‖ := lt_of_le_of_ne (norm_nonneg _) hne.symm
  have hbal : ‖v t‖ ^ 2 = μ * 1 / R := by
    rw [hsq, mul_one]
  have htl := kepler_third_law h.mu_pos one_pos h.radius_pos hv hbal rfl
  rwa [mul_one] at htl

/-! ## E. Units

With `l, s > 0` new length and time units per old unit (kilometres to metres `l = 1000`, seconds
to hours `s = 1 / 3600`), a coordinate of dimension `L^a T^b` is multiplied by `l ^ a * s ^ b`:
lengths by `l`, times by `s`, speeds by `l / s`, the gravitational parameter (`L³ T⁻²`) by
`l ^ 3 / s ^ 2`. In the new units the state at the new time `τ` is the old state at `τ / s`. -/

/-- The premises are preserved by a change of units with the gravitational parameter scaled by
`l ^ 3 / s ^ 2` and the radius by `l`. -/
lemma IsCircularOrbit.unitChange {μ R l s : ℝ} {r v : ℝ → ℂ} (h : IsCircularOrbit μ R r v)
    (hl : 0 < l) (hs : 0 < s) :
    IsCircularOrbit (l ^ 3 / s ^ 2 * μ) (l * R) (fun τ => l • r (τ / s))
      (fun τ => (l / s) • v (τ / s)) := by
  have hμ := h.mu_pos
  have hR := h.radius_pos
  have hsne : s ≠ 0 := ne_of_gt hs
  have hlne : l ≠ 0 := ne_of_gt hl
  have hRne : R ≠ 0 := ne_of_gt hR
  have hdiv : ∀ τ, HasDerivAt (fun τ : ℝ => τ / s) (1 / s) τ := fun τ =>
    (hasDerivAt_id' τ).div_const s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · exact mul_pos hl hR
  · intro τ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl, h.norm_eq]
  · intro τ
    have hcomp : HasDerivAt (fun τ => r (τ / s)) ((1 / s) • v (τ / s)) τ :=
      HasDerivAt.scomp τ (h.hasDerivAt_pos (τ / s)) (hdiv τ)
    have hsmul := HasDerivAt.const_smul l hcomp
    have hscal : l • ((1 / s) • v (τ / s)) = (l / s) • v (τ / s) := by
      rw [← smul_assoc, smul_eq_mul, mul_one_div]
    rw [hscal] at hsmul
    exact hsmul
  · intro τ
    show HasDerivAt (fun τ => (l / s) • v (τ / s))
      (-((l ^ 3 / s ^ 2 * μ) / ‖l • r (τ / s)‖ ^ 3) • (l • r (τ / s))) τ
    have hnorm_new : ‖l • r (τ / s)‖ = l * R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl, h.norm_eq]
    rw [hnorm_new]
    have hcompv : HasDerivAt (fun τ => v (τ / s))
        ((1 / s) • (-(μ / ‖r (τ / s)‖ ^ 3) • r (τ / s))) τ :=
      HasDerivAt.scomp τ (h.hasDerivAt_vel (τ / s)) (hdiv τ)
    have hsmulv := HasDerivAt.const_smul (l / s) hcompv
    rw [h.norm_eq] at hsmulv
    have hscalv : (l / s) • (1 / s) • (-(μ / R ^ 3) • r (τ / s))
        = (-((l ^ 3 / s ^ 2 * μ) / (l * R) ^ 3)) • (l • r (τ / s)) := by
      rw [← smul_assoc, ← smul_assoc, ← smul_assoc]
      simp only [smul_eq_mul]
      congr 1
      field_simp
    rw [hscalv] at hsmulv
    exact hsmulv

/-- Wrong time units are rejected: a change of time unit (`s ≠ 1`) that leaves out the factor
`s⁻²` of the gravitational parameter gives no circular orbit. -/
lemma IsCircularOrbit.not_wrong_time_unit {μ R l s : ℝ} {r v : ℝ → ℂ}
    (h : IsCircularOrbit μ R r v) (hl : 0 < l) (hs : 0 < s) (hs1 : s ≠ 1) :
    ¬ IsCircularOrbit (l ^ 3 * μ) (l * R) (fun τ => l • r (τ / s))
      (fun τ => (l / s) • v (τ / s)) := by
  intro hw
  have htrue := h.norm_vel_sq 0
  have hwrong := hw.norm_vel_sq 0
  simp only [zero_div] at hwrong
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hl hs), mul_pow, htrue] at hwrong
  have hμR : μ / R ≠ 0 := ne_of_gt (div_pos h.mu_pos h.radius_pos)
  have hlne : l ≠ 0 := ne_of_gt hl
  have hsne : s ≠ 0 := ne_of_gt hs
  have hRne : R ≠ 0 := ne_of_gt h.radius_pos
  have hrhs : l ^ 3 * μ / (l * R) = l ^ 2 * (μ / R) := by
    field_simp
  rw [hrhs] at hwrong
  have hsq : (l / s) ^ 2 = l ^ 2 := mul_right_cancel₀ hμR hwrong
  rw [div_pow] at hsq
  have hl2 : (l ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hlne
  have hs2ne : s ^ 2 ≠ 0 := pow_ne_zero 2 hsne
  rw [div_eq_iff hs2ne] at hsq
  have hs2 : s ^ 2 = 1 := mul_left_cancel₀ hl2 (by rw [mul_one]; exact hsq.symm)
  have hs1eq : s = 1 := by
    have hfac : (s - 1) * (s + 1) = 0 := by
      have hring : (s - 1) * (s + 1) = s ^ 2 - 1 := by ring
      rw [hring, hs2]
      norm_num
    rcases mul_eq_zero.mp hfac with hcase | hcase
    · linarith
    · linarith
  exact hs1 hs1eq

/-- Consistent speed and period units: under the change of units the circular speed `√(μ / R)`
scales by `l / s` and the period `2 π R / √(μ / R)` by `s`. -/
lemma speed_period_unitChange {μ R l s : ℝ} (hμ : 0 < μ) (hR : 0 < R) (hl : 0 < l)
    (hs : 0 < s) :
    Real.sqrt (l ^ 3 / s ^ 2 * μ / (l * R)) = l / s * Real.sqrt (μ / R) ∧
      2 * Real.pi * (l * R) / Real.sqrt (l ^ 3 / s ^ 2 * μ / (l * R)) =
        s * (2 * Real.pi * R / Real.sqrt (μ / R)) := by
  have hμR : 0 < μ / R := div_pos hμ hR
  have hls : 0 < l / s := div_pos hl hs
  have hsne : s ≠ 0 := ne_of_gt hs
  have hlne : l ≠ 0 := ne_of_gt hl
  have hRne : R ≠ 0 := ne_of_gt hR
  have harg : l ^ 3 / s ^ 2 * μ / (l * R) = (l / s) ^ 2 * (μ / R) := by
    field_simp
  have hsqrt : Real.sqrt (l ^ 3 / s ^ 2 * μ / (l * R)) = l / s * Real.sqrt (μ / R) := by
    rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hls.le]
  refine ⟨hsqrt, ?_⟩
  rw [hsqrt]
  have hsqne : Real.sqrt (μ / R) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hμR)
  have hlsne : l / s ≠ 0 := ne_of_gt hls
  field_simp

/-! ## F. Planar to spatial state -/

/-- Body components `(x, y, 0)` of the point `x + y i` of the orbit plane, the plane of the first
two body axes. -/
def planarToBody (z : ℂ) : Fin 3 → ℝ :=
  ![z.re, z.im, 0]

/-- Inertial components `Q (x, y, 0)` of the planar state `z t`, for the orbit-plane frame of
orientation `Q ∈ SO(3)` (passive free-vector map of the frame dictionary). -/
def spatialState (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (z : ℝ → ℂ) (t : ℝ) :
    Fin 3 → ℝ :=
  bodyToInertialVec Q (planarToBody (z t))

/-- The planar-to-spatial map preserves Euclidean length: `X ⬝ᵥ X = ‖z‖ ^ 2`. -/
lemma dotProduct_spatialState (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (z : ℝ → ℂ)
    (t : ℝ) : spatialState Q z t ⬝ᵥ spatialState Q z t = ‖z t‖ ^ 2 := by
  simp only [spatialState, bodyToInertialVec_dotProduct, planarToBody]
  have hcc : ‖z t‖ ^ 2 = (z t).re * (z t).re + (z t).im * (z t).im :=
    RCLike.norm_sq_eq_def
  rw [hcc]
  simp

/-- The spatial state stays in the orbit plane: it is orthogonal to the plane normal `Q e₃`. -/
lemma spatialState_dotProduct_normal (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (z : ℝ → ℂ) (t : ℝ) : spatialState Q z t ⬝ᵥ bodyToInertialVec Q ![0, 0, 1] = 0 := by
  simp only [spatialState, bodyToInertialVec_dotProduct, planarToBody]
  simp

/-- The planar-to-spatial map commutes with time derivatives. -/
lemma hasDerivAt_spatialState (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {z : ℝ → ℂ}
    {w : ℂ} {t : ℝ} (hz : HasDerivAt z w t) :
    HasDerivAt (spatialState Q z) (bodyToInertialVec Q (planarToBody w)) t := by
  let L : ℂ →L[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun z => bodyToInertialVec Q (planarToBody z)
      map_add' := fun a b => by
        have hadd : planarToBody (a + b) = planarToBody a + planarToBody b := by
          ext i
          fin_cases i <;> simp [planarToBody, Complex.add_re, Complex.add_im]
        simp only [bodyToInertialVec, hadd, Matrix.mulVec_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        have hsmul : planarToBody (c • x) = c • planarToBody x := by
          ext i
          fin_cases i <;> simp [planarToBody]
        simp only [bodyToInertialVec, hsmul, Matrix.mulVec_smul]
      cont := by
        have hvec : Continuous fun z : ℂ => ![z.re, z.im, (0 : ℝ)] := by
          rw [continuous_pi_iff]
          intro i
          fin_cases i
          · exact Complex.continuous_re.congr (fun z => by simp)
          · exact Complex.continuous_im.congr (fun z => by simp)
          · exact (continuous_const : Continuous fun _ : ℂ => (0 : ℝ)).congr
              (fun z => by simp)
        have hmul : Continuous fun v : Fin 3 → ℝ
            => (Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v := by
          rw [continuous_pi_iff]
          intro i
          simp only [Matrix.mulVec, dotProduct]
          exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))
        simp only [bodyToInertialVec, planarToBody]
        exact hmul.comp hvec }
  have hL := HasFDerivAt.comp_hasDerivAt t L.hasFDerivAt hz
  have hfun : ⇑L ∘ z = spatialState Q z := rfl
  have hval : L w = bodyToInertialVec Q (planarToBody w) := rfl
  rw [hfun, hval] at hL
  exact hL

/-- The spatial position of a circular orbit stays at Euclidean distance `R` from the center. -/
lemma IsCircularOrbit.dotProduct_spatialState {μ R : ℝ} {r v : ℝ → ℂ}
    (h : IsCircularOrbit μ R r v) (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : ℝ) :
    spatialState Q r t ⬝ᵥ spatialState Q r t = R ^ 2 := by
  rw [OrbitalPorts.dotProduct_spatialState, h.norm_eq]

/-- The inverse-square law in inertial components: the spatial velocity has derivative
`-(μ / |X| ^ 3) • X` with `X` the spatial position and `|X| = √(X ⬝ᵥ X)`. -/
lemma IsCircularOrbit.hasDerivAt_spatialVelocity {μ R : ℝ} {r v : ℝ → ℂ}
    (h : IsCircularOrbit μ R r v) (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (t : ℝ) :
    HasDerivAt (spatialState Q v)
      (-(μ / Real.sqrt (spatialState Q r t ⬝ᵥ spatialState Q r t) ^ 3) • spatialState Q r t)
      t := by
  have h1 := OrbitalPorts.hasDerivAt_spatialState Q (h.hasDerivAt_vel t)
  have hsqrt : Real.sqrt (spatialState Q r t ⬝ᵥ spatialState Q r t) = ‖r t‖ := by
    rw [OrbitalPorts.dotProduct_spatialState]
    exact Real.sqrt_sq (norm_nonneg _)
  have hlin : bodyToInertialVec Q (planarToBody (-(μ / ‖r t‖ ^ 3) • r t))
      = (-(μ / ‖r t‖ ^ 3)) • bodyToInertialVec Q (planarToBody (r t)) := by
    have hsmul : planarToBody (-(μ / ‖r t‖ ^ 3) • r t)
        = (-(μ / ‖r t‖ ^ 3)) • planarToBody (r t) := by
      have gen : ∀ (c : ℝ) (z : ℂ), planarToBody (c • z) = c • planarToBody z := by
        intro c z
        ext i
        fin_cases i <;> simp [planarToBody]
      exact gen _ _
    simp only [bodyToInertialVec, hsmul, Matrix.mulVec_smul]
  rw [hsqrt]
  rw [hlin] at h1
  exact h1

/-! ## G. The eccentricity vector and the energy identity -/

/-- Eccentricity vector `e = (v ⨯₃ h) / μ - x / r` of the state `(x, v)`, with `h = x ⨯₃ v` the
specific angular momentum and `r = |x|`. Declared for `μ > 0` and `r > 0`; at `x = 0` or `μ = 0`
Lean's convention `1 / 0 = 0` gives a meaningless value. -/
noncomputable def eccentricityVector (μ : ℝ) (x v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (1 / μ) • (v ⨯₃ (x ⨯₃ v)) - (1 / radius x) • x

/-- Eccentricity `|e| = √(e ⬝ᵥ e)`, the Euclidean length of the eccentricity vector. -/
noncomputable def eccentricity (μ : ℝ) (x v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (eccentricityVector μ x v ⬝ᵥ eccentricityVector μ x v)

/-- Dot squares are nonnegative. -/
private lemma dot_sq_nonneg (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [vec3_dotProduct]
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

/-- The dot square of a nonzero vector is positive. -/
private lemma dot_sq_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dot_sq_nonneg v) (Ne.symm fun h => hv (dotProduct_self_eq_zero.mp h))

/-- The squared radius is the dot square of the position. -/
private lemma radius_sq (x : Fin 3 → ℝ) : (radius x) ^ 2 = x ⬝ᵥ x :=
  Real.sq_sqrt (dot_sq_nonneg x)

/-- `|v ⨯₃ h|² = |v|² |h|²` for `h = x ⨯₃ v`, since `v ⬝ᵥ h = 0`. -/
private lemma cross_h_dot_self (x v : Fin 3 → ℝ) :
    (v ⨯₃ (x ⨯₃ v)) ⬝ᵥ (v ⨯₃ (x ⨯₃ v)) = (v ⬝ᵥ v) * ((x ⨯₃ v) ⬝ᵥ (x ⨯₃ v)) := by
  have h1 : v ⬝ᵥ (x ⨯₃ v) = 0 := dot_cross_self x v
  rw [cross_dot_cross, h1]
  simp

/-- `(v ⨯₃ h) ⬝ᵥ x = |h|²` for `h = x ⨯₃ v`, by the cyclic triple product. -/
private lemma cross_h_dot_x (x v : Fin 3 → ℝ) :
    (v ⨯₃ (x ⨯₃ v)) ⬝ᵥ x = (x ⨯₃ v) ⬝ᵥ (x ⨯₃ v) := by
  rw [dotProduct_comm]
  rw [triple_product_permutation x v (x ⨯₃ v)]
  rw [triple_product_permutation v (x ⨯₃ v) x]

/-- The energy identity of the eccentricity vector: for `μ > 0` and `r > 0`,
`|e|² = 1 + 2 E |h|² / μ²` with `h = x ⨯₃ v`. It is algebra at one state, not a conservation law. -/
lemma eccentricity_sq {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ) (hr : 0 < radius x) :
    eccentricity μ x v ^ 2 =
      1 + 2 * specificEnergy μ x v * ((x ⨯₃ v) ⬝ᵥ (x ⨯₃ v)) / μ ^ 2 := by
  have hμ' : μ ≠ 0 := ne_of_gt hμ
  have hr' : radius x ≠ 0 := ne_of_gt hr
  have hxx : x ⬝ᵥ x = (radius x) ^ 2 := (radius_sq x).symm
  have e1 := cross_h_dot_self x v
  have e2 := cross_h_dot_x x v
  have e3 : x ⬝ᵥ (v ⨯₃ (x ⨯₃ v)) = (x ⨯₃ v) ⬝ᵥ (x ⨯₃ v) := by
    rw [dotProduct_comm x]
    exact e2
  have hexpand : eccentricityVector μ x v ⬝ᵥ eccentricityVector μ x v =
      (v ⬝ᵥ v) * ((x ⨯₃ v) ⬝ᵥ (x ⨯₃ v)) / μ ^ 2
        - 2 * (((x ⨯₃ v) ⬝ᵥ (x ⨯₃ v)) / μ / radius x) + 1 := by
    simp only [eccentricityVector, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, e1, e2, e3, hxx, smul_eq_mul]
    field_simp
    ring
  unfold eccentricity
  rw [Real.sq_sqrt (dot_sq_nonneg _), hexpand]
  unfold specificEnergy speedSq
  field_simp
  ring

/-- A bound state with nonzero specific angular momentum has `0 ≤ |e| < 1` and `a > 0`: for
`μ > 0`, `E < 0` and `h = x ⨯₃ v ≠ 0` (which forces `r > 0`). No ellipse is constructed. -/
lemma eccentricity_lt_one_and_semiMajorAxis_pos {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ)
    (hE : specificEnergy μ x v < 0) (hh : x ⨯₃ v ≠ 0) :
    0 ≤ eccentricity μ x v ∧ eccentricity μ x v < 1 ∧ 0 < semiMajorAxis μ x v := by
  have hx : x ≠ 0 := by
    intro h
    apply hh
    rw [h]
    simp
  have hr : 0 < radius x := by
    unfold radius
    exact Real.sqrt_pos.mpr (dot_sq_pos hx)
  have hsq := eccentricity_sq (v := v) hμ hr
  have hhdot : 0 < (x ⨯₃ v) ⬝ᵥ (x ⨯₃ v) := dot_sq_pos hh
  have h2E : (2 : ℝ) * specificEnergy μ x v < 0 := mul_neg_of_pos_of_neg (by norm_num) hE
  have hterm : 2 * specificEnergy μ x v * ((x ⨯₃ v) ⬝ᵥ (x ⨯₃ v)) / μ ^ 2 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h2E hhdot) (pow_pos hμ 2)
  have he2 : eccentricity μ x v ^ 2 < 1 := by
    rw [hsq]
    linarith
  have he_nonneg : 0 ≤ eccentricity μ x v := Real.sqrt_nonneg _
  have h1sq : eccentricity μ x v ^ 2 < 1 ^ 2 := by
    rw [one_pow]
    exact he2
  have he_lt : eccentricity μ x v < 1 :=
    lt_of_le_of_lt (le_abs_self _) (abs_lt_of_sq_lt_sq h1sq (by norm_num))
  have ha : 0 < semiMajorAxis μ x v := by
    unfold semiMajorAxis
    exact div_pos_of_neg_of_neg (neg_lt_zero.mpr hμ) h2E
  exact ⟨he_nonneg, he_lt, ha⟩

/-! ## H. Undefined pericenter and node directions -/

/-- Ascending-node vector `n = k ⨯₃ h` of the state `(x, v)`, with `k = (0, 0, 1)` the pole of the
reference plane and `h = x ⨯₃ v`. The node direction `n / |n|` is undefined where `n = 0`. -/
def nodeVector (x v : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 0, 1] ⨯₃ (x ⨯₃ v)

/-- The pericenter direction `e / |e|` is undefined exactly for circular states: for `μ > 0` and
`r > 0`, `e = 0` iff the velocity is transverse (`x ⬝ᵥ v = 0`) at circular speed
(`|v|² = μ / r`). -/
lemma eccentricityVector_eq_zero_iff {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ) (hr : 0 < radius x) :
    eccentricityVector μ x v = 0 ↔ x ⬝ᵥ v = 0 ∧ speedSq v = μ / radius x := by
  have hμ' : μ ≠ 0 := ne_of_gt hμ
  have hr' : radius x ≠ 0 := ne_of_gt hr
  have hxx : x ⬝ᵥ x = (radius x) ^ 2 := (radius_sq x).symm
  constructor
  · intro he
    have hsub : (1 / μ) • (v ⨯₃ (x ⨯₃ v)) = (1 / radius x) • x := by
      have h := he
      unfold eccentricityVector at h
      exact sub_eq_zero.mp h
    have huv : (v ⨯₃ (x ⨯₃ v)) ⬝ᵥ v = 0 := by
      rw [dotProduct_comm]
      exact dot_self_cross v _
    have hdotv := congrArg (fun w => w ⬝ᵥ v) hsub
    simp only [smul_dotProduct, huv, smul_eq_mul, mul_zero] at hdotv
    have hxv : x ⬝ᵥ v = 0 :=
      (mul_eq_zero.mp hdotv.symm).resolve_left (div_ne_zero one_ne_zero hr')
    have hdotx := congrArg (fun w => w ⬝ᵥ x) hsub
    simp only [smul_dotProduct, cross_h_dot_x, hxx, smul_eq_mul] at hdotx
    have hhl : (x ⨯₃ v) ⬝ᵥ (x ⨯₃ v) = μ * radius x := by
      have h2 := congrArg (fun t => μ * radius x * t) hdotx
      simp only [← mul_assoc] at h2
      have eA : μ * radius x * (1 / μ) = radius x := by field_simp
      have eB : μ * radius x * (1 / radius x) = μ := by field_simp
      rw [eA, eB] at h2
      have h3 : ((x ⨯₃ v) ⬝ᵥ (x ⨯₃ v)) * radius x = (μ * radius x) * radius x := by
        linear_combination h2
      exact mul_right_cancel₀ hr' h3
    have hcross := cross_dot_cross x v x v
    rw [hxv, hxx] at hcross
    simp only [zero_mul, sub_zero] at hcross
    have hSr : (v ⬝ᵥ v) * radius x = μ := by
      have h := hcross.symm.trans hhl
      have h2 : ((v ⬝ᵥ v) * radius x) * radius x = μ * radius x := by
        linear_combination h
      exact mul_right_cancel₀ hr' h2
    refine ⟨hxv, ?_⟩
    simp only [speedSq]
    rw [eq_div_iff_mul_eq hr']
    exact hSr
  · rintro ⟨hxv, hS⟩
    simp only [speedSq] at hS
    have hexp : v ⨯₃ (x ⨯₃ v) = (v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v :=
      cross_cross_eq_smul_sub_smul' v x v
    have hcoeff : (1 / μ) * (v ⬝ᵥ v) = 1 / radius x := by
      rw [hS]
      field_simp
    unfold eccentricityVector
    rw [hexp, hxv]
    simp only [zero_smul, sub_zero, smul_smul, hcoeff, sub_self]

/-- Radial boundary: a state with `h = x ⨯₃ v = 0` and `r > 0` has `e = -x / r` and `|e| = 1`,
whatever its energy, so `h ≠ 0` cannot be dropped from
`eccentricity_lt_one_and_semiMajorAxis_pos`. -/
lemma eccentricityVector_of_cross_eq_zero {μ : ℝ} {x v : Fin 3 → ℝ} (hr : 0 < radius x)
    (hh : x ⨯₃ v = 0) :
    eccentricityVector μ x v = -((1 / radius x) • x) ∧ eccentricity μ x v = 1 := by
  have hr' : radius x ≠ 0 := ne_of_gt hr
  have hxx : x ⬝ᵥ x = (radius x) ^ 2 := (radius_sq x).symm
  have hv0 : v ⨯₃ (x ⨯₃ v) = 0 := by
    rw [hh]
    simp
  have he : eccentricityVector μ x v = -((1 / radius x) • x) := by
    unfold eccentricityVector
    rw [hv0]
    simp
  have hdot : eccentricityVector μ x v ⬝ᵥ eccentricityVector μ x v = 1 := by
    rw [he]
    simp only [neg_dotProduct, dotProduct_neg, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hxx]
    field_simp
  have hecc : eccentricity μ x v = 1 := by
    unfold eccentricity
    rw [hdot]
    exact Real.sqrt_one
  exact ⟨he, hecc⟩

/-- The node direction is undefined exactly when the specific angular momentum lies along the
pole: `n = 0` iff `h₁ = h₂ = 0` for `h = x ⨯₃ v`, an orbit in the reference plane or `h = 0`. -/
lemma nodeVector_eq_zero_iff (x v : Fin 3 → ℝ) :
    nodeVector x v = 0 ↔ (x ⨯₃ v) 0 = 0 ∧ (x ⨯₃ v) 1 = 0 := by
  have hcross := cross_apply (![0, 0, 1] : Fin 3 → ℝ) (x ⨯₃ v)
  have n0 : nodeVector x v 0 = -((x ⨯₃ v) 1) := by
    unfold nodeVector
    rw [hcross]
    simp
  have n1 : nodeVector x v 1 = (x ⨯₃ v) 0 := by
    unfold nodeVector
    rw [hcross]
    simp
  have nvec : nodeVector x v = ![-((x ⨯₃ v) 1), (x ⨯₃ v) 0, 0] := by
    unfold nodeVector
    rw [hcross]
    ext i
    fin_cases i <;> simp
  constructor
  · intro h
    have h0 : (x ⨯₃ v) 0 = 0 := by
      have h1' := congrFun h 1
      rw [n1] at h1'
      simpa using h1'
    have h1 : (x ⨯₃ v) 1 = 0 := by
      have h0' := congrFun h 0
      rw [n0] at h0'
      simpa using h0'
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    rw [nvec, h0, h1]
    ext i
    fin_cases i <;> simp

/-! ## I. Frame covariance -/

/-- Chart-free: a proper rotation `R` of the frame rotates the eccentricity vector with the
state, `e(R x, R v) = R e(x, v)`, and keeps the eccentricity `|e|`. -/
lemma eccentricityVector_mulVec {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (μ : ℝ) (x v : Fin 3 → ℝ) :
    eccentricityVector μ (R *ᵥ x) (R *ᵥ v) = R *ᵥ eccentricityVector μ x v ∧
      eccentricity μ (R *ᵥ x) (R *ᵥ v) = eccentricity μ x v := by
  have hQ : R ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hR).1
  have hdet : R.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp hR).2
  have h2 : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hQ
  have orth_self : ∀ (y : Fin 3 → ℝ), (R *ᵥ y) ⬝ᵥ (R *ᵥ y) = y ⬝ᵥ y := by
    intro y
    calc (R *ᵥ y) ⬝ᵥ (R *ᵥ y) = ((R *ᵥ y) ᵥ* R) ⬝ᵥ y := dotProduct_mulVec _ _ _
      _ = (y ᵥ* (Rᵀ * R)) ⬝ᵥ y := by rw [vecMul_mulVec]
      _ = y ⬝ᵥ y := by rw [h2, vecMul_one]
  have hcross : ∀ (a b : Fin 3 → ℝ), (R *ᵥ a) ⨯₃ (R *ᵥ b) = R *ᵥ (a ⨯₃ b) := by
    intro a b
    have h := Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup hQ a b
    rw [hdet] at h
    simpa using h
  have hrad : radius (R *ᵥ x) = radius x := by
    unfold radius
    rw [orth_self]
  have hvec : eccentricityVector μ (R *ᵥ x) (R *ᵥ v) = R *ᵥ eccentricityVector μ x v := by
    unfold eccentricityVector
    rw [hcross, hcross, hrad, ← mulVec_smul, ← mulVec_smul, ← mulVec_sub]
  have hecc : eccentricity μ (R *ᵥ x) (R *ᵥ v) = eccentricity μ x v := by
    unfold eccentricity
    rw [hvec, orth_self]
  exact ⟨hvec, hecc⟩

/-! ## J. The planar Kepler arc premises -/

open Units.EngineeringFrames (bodyToInertialVec_cross)

/-- The planar point `x t + y t i` of two real coordinate functions, in the complex carrier of
`spatialState`. -/
def planarPath (x y : ℝ → ℝ) (t : ℝ) : ℂ :=
  ⟨x t, y t⟩

/-- Premises of a planar Kepler coast with gravitational parameter `μ` over `[t₀, t₁]`: `μ > 0`
and the fields of the upstream Physlib `KeplerArc` for the coordinate functions `x, y, vx, vy`.
No conservation law is a premise. -/
structure IsPlanarKeplerArc (μ t₀ t₁ : ℝ) (x y vx vy : ℝ → ℝ) : Prop where
  /-- The gravitational parameter is positive: the central force attracts. -/
  mu_pos : 0 < μ
  /-- The coast takes positive time. -/
  time_order : t₀ < t₁
  /-- The coast stays away from the attracting center. -/
  radius_pos : ∀ t ∈ Set.Icc t₀ t₁, 0 < Real.sqrt (x t ^ 2 + y t ^ 2)
  /-- The first position derivative is the first velocity component. -/
  dx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt x (vx t) t
  /-- The second position derivative is the second velocity component. -/
  dy : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt y (vy t) t
  /-- The first velocity derivative is the Newtonian central acceleration. -/
  dvx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt vx (-μ * x t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3) t
  /-- The second velocity derivative is the Newtonian central acceleration. -/
  dvy : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt vy (-μ * y t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3) t

private lemma planarVec_cross (a b c d : ℝ) :
    ![a, b, 0] ⨯₃ ![c, d, 0] = (a * d - b * c) • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [cross_apply, Pi.smul_apply, smul_eq_mul]

private lemma hasDerivAt_planarPath {x y : ℝ → ℝ} {vx vy t : ℝ}
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t) :
    HasDerivAt (planarPath x y) ⟨vx, vy⟩ t := by
  have hdecomp : planarPath x y = fun t => (x t : ℂ) + (y t : ℂ) * Complex.I := by
    ext t
    exact Complex.mk_eq_add_mul_I (x t) (y t)
  have hval : (⟨vx, vy⟩ : ℂ) = (vx : ℂ) + (vy : ℂ) * Complex.I :=
    Complex.mk_eq_add_mul_I vx vy
  rw [hdecomp, hval]
  exact hx.ofReal_comp.add (hy.ofReal_comp.mul_const Complex.I)

/-! ## K. Energy and angular momentum in the spatial plane -/

/-- The spatial position `Q (x, y, 0)` is at the planar distance `√(x² + y²)` from the center. -/
lemma radius_spatialState_planarPath (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x y : ℝ → ℝ) (t : ℝ) :
    radius (spatialState Q (planarPath x y) t) = Real.sqrt (x t ^ 2 + y t ^ 2) := by
  have hcc : ‖planarPath x y t‖ ^ 2 = x t * x t + y t * y t :=
    RCLike.norm_sq_eq_def
  simp only [radius, dotProduct_spatialState, hcc]
  congr 1
  ring

/-- **Energy in the upstream normalization.** The planar energy `vx² + vy² - 2 μ / √(x² + y²)` is
twice the specific energy `|V|² / 2 - μ / |X|` of the spatial state: the factor two is kept. -/
lemma two_mul_specificEnergy_spatialState (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (μ : ℝ)
    (x y vx vy : ℝ → ℝ) (t : ℝ) :
    2 * specificEnergy μ (spatialState Q (planarPath x y) t)
        (spatialState Q (planarPath vx vy) t) =
      vx t ^ 2 + vy t ^ 2 - 2 * μ / Real.sqrt (x t ^ 2 + y t ^ 2) := by
  have hV : spatialState Q (planarPath vx vy) t ⬝ᵥ spatialState Q (planarPath vx vy) t
      = vx t * vx t + vy t * vy t := by
    have hcc : ‖planarPath vx vy t‖ ^ 2 = vx t * vx t + vy t * vy t :=
      RCLike.norm_sq_eq_def
    rw [dotProduct_spatialState, hcc]
  simp only [specificEnergy, speedSq, hV, radius_spatialState_planarPath]
  ring

/-- **Energy transport.** Equal planar energies at `t₀` and `t₁`, in the upstream normalization
(the conclusion of the upstream energy conservation lemma), give equal specific energies of the
spatial states. -/
lemma specificEnergy_spatialState_eq_of_energy_eq (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (μ : ℝ) {x y vx vy : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hE : vx t₀ ^ 2 + vy t₀ ^ 2 - 2 * μ / Real.sqrt (x t₀ ^ 2 + y t₀ ^ 2) =
      vx t₁ ^ 2 + vy t₁ ^ 2 - 2 * μ / Real.sqrt (x t₁ ^ 2 + y t₁ ^ 2)) :
    specificEnergy μ (spatialState Q (planarPath x y) t₀)
        (spatialState Q (planarPath vx vy) t₀) =
      specificEnergy μ (spatialState Q (planarPath x y) t₁)
        (spatialState Q (planarPath vx vy) t₁) := by
  have h0 := two_mul_specificEnergy_spatialState Q μ x y vx vy t₀
  have h1 := two_mul_specificEnergy_spatialState Q μ x y vx vy t₁
  rw [hE] at h0
  have h2 : 2 * specificEnergy μ (spatialState Q (planarPath x y) t₀)
        (spatialState Q (planarPath vx vy) t₀)
      = 2 * specificEnergy μ (spatialState Q (planarPath x y) t₁)
        (spatialState Q (planarPath vx vy) t₁) := by rw [h0, h1]
  exact mul_left_cancel₀ (by norm_num) h2

/-- **Angular momentum along the oriented normal.** The specific angular momentum `X ⨯₃ V` of the
spatial state is the planar signed angular momentum `x vy - y vx` times the normal `Q e₃`. -/
lemma cross_spatialState (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x y vx vy : ℝ → ℝ)
    (t : ℝ) :
    spatialState Q (planarPath x y) t ⨯₃ spatialState Q (planarPath vx vy) t =
      (x t * vy t - y t * vx t) • bodyToInertialVec Q ![0, 0, 1] := by
  have hxy : planarToBody (planarPath x y t) = ![x t, y t, 0] := rfl
  have hvv : planarToBody (planarPath vx vy t) = ![vx t, vy t, 0] := rfl
  have hcross : planarToBody (planarPath x y t) ⨯₃ planarToBody (planarPath vx vy t)
      = (x t * vy t - y t * vx t) • ![0, 0, 1] := by
    rw [hxy, hvv, planarVec_cross]
  simp only [spatialState, ← bodyToInertialVec_cross, hcross]
  simp only [bodyToInertialVec, Matrix.mulVec_smul]

/-- **Orientation is preserved.** The component of `X ⨯₃ V` along the oriented normal `Q e₃` is
the planar signed angular momentum `x vy - y vx`. -/
lemma cross_spatialState_dotProduct_normal (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x y vx vy : ℝ → ℝ) (t : ℝ) :
    (spatialState Q (planarPath x y) t ⨯₃ spatialState Q (planarPath vx vy) t) ⬝ᵥ
        bodyToInertialVec Q ![0, 0, 1] = x t * vy t - y t * vx t := by
  have hn : bodyToInertialVec Q ![0, 0, 1] ⬝ᵥ bodyToInertialVec Q ![0, 0, 1] = 1 := by
    rw [bodyToInertialVec_dotProduct]
    simp [dotProduct, Fin.sum_univ_three]
  rw [cross_spatialState, smul_dotProduct, hn, smul_eq_mul, mul_one]

/-- **Angular-momentum transport.** Equal planar signed angular momenta at `t₀` and `t₁` (the
conclusion of the upstream angular conservation lemma) give equal angular-momentum vectors of
the spatial states. -/
lemma cross_spatialState_eq_of_angular_eq (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {x y vx vy : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hL : x t₀ * vy t₀ - y t₀ * vx t₀ = x t₁ * vy t₁ - y t₁ * vx t₁) :
    spatialState Q (planarPath x y) t₀ ⨯₃ spatialState Q (planarPath vx vy) t₀ =
      spatialState Q (planarPath x y) t₁ ⨯₃ spatialState Q (planarPath vx vy) t₁ := by
  rw [cross_spatialState, cross_spatialState, hL]

/-- **A reflection reverses the orientation.** For an orthogonal `P` with `det P = -1`, the
component of `P (x, y, 0) ⨯₃ P (vx, vy, 0)` along the mapped normal `P e₃` is
`-(x vy - y vx)`. -/
lemma cross_dotProduct_normal_of_det_eq_neg_one {P : Matrix (Fin 3) (Fin 3) ℝ}
    (hP : P ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hdet : P.det = -1) (x y vx vy : ℝ) :
    ((P *ᵥ planarToBody ⟨x, y⟩) ⨯₃ (P *ᵥ planarToBody ⟨vx, vy⟩)) ⬝ᵥ (P *ᵥ ![0, 0, 1]) =
      -(x * vy - y * vx) := by
  have hxy : planarToBody (⟨x, y⟩ : ℂ) = ![x, y, 0] := rfl
  have hvv : planarToBody (⟨vx, vy⟩ : ℂ) = ![vx, vy, 0] := rfl
  have hcross : planarToBody (⟨x, y⟩ : ℂ) ⨯₃ planarToBody (⟨vx, vy⟩ : ℂ)
      = (x * vy - y * vx) • ![0, 0, 1] := by
    rw [hxy, hvv, planarVec_cross]
  have hT : Pᵀ * P = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hP
  have hn : (P *ᵥ ![0, 0, 1]) ⬝ᵥ (P *ᵥ ![0, 0, 1]) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hT,
      Matrix.one_mulVec]
    simp [dotProduct, Fin.sum_univ_three]
  rw [Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup hP, hdet, hcross, Matrix.mulVec_smul,
    smul_dotProduct, smul_dotProduct, hn, smul_eq_mul, smul_eq_mul]
  ring

/-! ## L. The spatial Kepler arc -/

/-- The embedded arc stays away from the center on `[t₀, t₁]`. -/
lemma IsPlanarKeplerArc.radius_spatialState_pos {μ t₀ t₁ : ℝ} {x y vx vy : ℝ → ℝ}
    (h : IsPlanarKeplerArc μ t₀ t₁ x y vx vy) (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    0 < radius (spatialState Q (planarPath x y) t) := by
  rw [radius_spatialState_planarPath]
  exact h.radius_pos t ht

/-- The spatial position has derivative the spatial velocity on `[t₀, t₁]`. -/
lemma IsPlanarKeplerArc.hasDerivAt_spatialPosition {μ t₀ t₁ : ℝ} {x y vx vy : ℝ → ℝ}
    (h : IsPlanarKeplerArc μ t₀ t₁ x y vx vy) (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    HasDerivAt (spatialState Q (planarPath x y)) (spatialState Q (planarPath vx vy) t) t := by
  exact hasDerivAt_spatialState Q (hasDerivAt_planarPath (h.dx t ht) (h.dy t ht))

/-- **The spatial Kepler equation.** The spatial velocity has derivative the inverse-square
attraction `-(μ / |X| ^ 3) • X` on `[t₀, t₁]`. -/
lemma IsPlanarKeplerArc.hasDerivAt_spatialVelocity {μ t₀ t₁ : ℝ} {x y vx vy : ℝ → ℝ}
    (h : IsPlanarKeplerArc μ t₀ t₁ x y vx vy) (Q : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    HasDerivAt (spatialState Q (planarPath vx vy))
      (-(μ / radius (spatialState Q (planarPath x y) t) ^ 3) •
        spatialState Q (planarPath x y) t) t := by
  have hvec : planarToBody (⟨-μ * x t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3,
        -μ * y t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3⟩ : ℂ)
      = (-(μ / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3)) • ![x t, y t, 0] := by
    have h0 : planarToBody (⟨-μ * x t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3,
          -μ * y t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3⟩ : ℂ)
        = ![-μ * x t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3,
          -μ * y t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3, 0] := rfl
    rw [h0]
    ext i
    fin_cases i
    · change -μ * x t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3
          = (-(μ / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3)) * x t
      ring
    · change -μ * y t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3
          = (-(μ / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3)) * y t
      ring
    · change (0 : ℝ) = (-(μ / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3)) * 0
      ring
  have hss : spatialState Q (planarPath x y) t = bodyToInertialVec Q ![x t, y t, 0] := rfl
  have hval : (-(μ / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3)) • spatialState Q (planarPath x y) t
      = bodyToInertialVec Q (planarToBody (⟨-μ * x t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3,
        -μ * y t / Real.sqrt (x t ^ 2 + y t ^ 2) ^ 3⟩ : ℂ)) := by
    rw [hvec]
    simp only [hss, bodyToInertialVec, Matrix.mulVec_smul]
  have hbase := hasDerivAt_spatialState Q (hasDerivAt_planarPath (h.dvx t ht) (h.dvy t ht))
  rw [radius_spatialState_planarPath, hval]
  exact hbase

/-! ## M. One equal-speed plane change -/

/-- Magnitude `|v₂ - v₁|` of the single impulse that changes the velocity from `v₁` to `v₂` at a
fixed position. -/
noncomputable def impulseMagnitude (v₁ v₂ : Fin 3 → ℝ) : ℝ := Real.sqrt (speedSq (v₂ - v₁))

/-- Equal-speed chord: if `|u|² = |w|² = s²` and `u ⬝ᵥ w = s² cos i`, then
`|w - u|² = 2 s² (1 - cos i)`. -/
lemma speedSq_sub_of_speedSq_eq {u w : Fin 3 → ℝ} {s i : ℝ} (hu : speedSq u = s ^ 2)
    (hw : speedSq w = s ^ 2) (huw : u ⬝ᵥ w = s ^ 2 * Real.cos i) :
    speedSq (w - u) = 2 * s ^ 2 * (1 - Real.cos i) := by
  unfold speedSq at hu hw ⊢
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hu, hw, huw,
    dotProduct_comm w u, huw]
  ring

/-- Nonnegative half-angle root: for `s ≥ 0` and `i ∈ [0, π]`,
`√(2 s² (1 - cos i)) = 2 s sin(i / 2)`. -/
lemma sqrt_two_mul_sq_mul_one_sub_cos {s i : ℝ} (hs : 0 ≤ s) (hi₀ : 0 ≤ i)
    (hiπ : i ≤ Real.pi) :
    Real.sqrt (2 * s ^ 2 * (1 - Real.cos i)) = 2 * s * Real.sin (i / 2) := by
  have hcos : Real.cos i ≤ 1 := Real.cos_le_one i
  have hsin : 0 ≤ Real.sin (i / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_nonneg])
  have hhalf : Real.sin (i / 2) = Real.sqrt ((1 - Real.cos i) / 2) :=
    Real.sin_half_eq_sqrt hi₀ (by linarith [Real.pi_nonneg])
  have hsq : Real.sin (i / 2) ^ 2 = (1 - Real.cos i) / 2 := by
    rw [hhalf, Real.sq_sqrt (by linarith)]
  have hLHS : 0 ≤ 2 * s ^ 2 * (1 - Real.cos i) := by
    have h1 : 0 ≤ 1 - Real.cos i := by linarith
    positivity
  have hRHS : 0 ≤ 2 * s * Real.sin (i / 2) := by positivity
  rw [Real.sqrt_eq_iff_eq_sq hLHS hRHS, mul_pow, hsq]
  ring

/-- One equal-speed plane change: at a node `x` off the attracting center, two velocities tangent
there (`x ⬝ᵥ v₁ = x ⬝ᵥ v₂ = 0`) with the same speed `v > 0`, whose specific angular momenta
`x ⨯₃ v₁` and `x ⨯₃ v₂` make the angle `i ∈ [0, π]`, differ by a single impulse of magnitude
`|v₂ - v₁| = 2 v sin(i / 2)`. This is the cost of this one specified impulse, not of an optimized
transfer. -/
lemma impulseMagnitude_planeChange {x v₁ v₂ : Fin 3 → ℝ} {v i : ℝ} (hr : 0 < radius x)
    (h₁ : x ⬝ᵥ v₁ = 0) (h₂ : x ⬝ᵥ v₂ = 0) (hv : 0 < v) (hv₁ : speedSq v₁ = v ^ 2)
    (hv₂ : speedSq v₂ = v ^ 2) (hi₀ : 0 ≤ i) (hiπ : i ≤ Real.pi)
    (hi : (x ⨯₃ v₁) ⬝ᵥ (x ⨯₃ v₂) =
      Real.cos i * (Real.sqrt ((x ⨯₃ v₁) ⬝ᵥ (x ⨯₃ v₁)) * Real.sqrt ((x ⨯₃ v₂) ⬝ᵥ (x ⨯₃ v₂)))) :
    impulseMagnitude v₁ v₂ = 2 * v * Real.sin (i / 2) := by
  have hv₁' : v₁ ⬝ᵥ v₁ = v ^ 2 := hv₁
  have hv₂' : v₂ ⬝ᵥ v₂ = v ^ 2 := hv₂
  have hc1 : v₁ ⬝ᵥ x = 0 := by rw [dotProduct_comm v₁ x, h₁]
  have hc2 : v₂ ⬝ᵥ x = 0 := by rw [dotProduct_comm v₂ x, h₂]
  have hXpos : 0 < x ⬝ᵥ x := by
    have hr' : 0 < Real.sqrt (x ⬝ᵥ x) := hr
    exact Real.sqrt_pos.mp hr'
  have hcross : (x ⨯₃ v₁) ⬝ᵥ (x ⨯₃ v₂) = (x ⬝ᵥ x) * (v₁ ⬝ᵥ v₂) := by
    rw [cross_dot_cross, h₂, hc1]
    ring
  have hn1 : (x ⨯₃ v₁) ⬝ᵥ (x ⨯₃ v₁) = (x ⬝ᵥ x) * v ^ 2 := by
    rw [cross_dot_cross, h₁, hc1, hv₁']
    ring
  have hn2 : (x ⨯₃ v₂) ⬝ᵥ (x ⨯₃ v₂) = (x ⬝ᵥ x) * v ^ 2 := by
    rw [cross_dot_cross, h₂, hc2, hv₂']
    ring
  have hsq1 : Real.sqrt ((x ⨯₃ v₁) ⬝ᵥ (x ⨯₃ v₁)) = radius x * v := by
    unfold radius
    rw [hn1, Real.sqrt_mul hXpos.le, Real.sqrt_sq hv.le]
  have hsq2 : Real.sqrt ((x ⨯₃ v₂) ⬝ᵥ (x ⨯₃ v₂)) = radius x * v := by
    unfold radius
    rw [hn2, Real.sqrt_mul hXpos.le, Real.sqrt_sq hv.le]
  have hr2 : radius x ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hXpos.le
  have hdot : v₁ ⬝ᵥ v₂ = v ^ 2 * Real.cos i := by
    have hX2 : (radius x * v) * (radius x * v) = (x ⬝ᵥ x) * v ^ 2 := by
      calc (radius x * v) * (radius x * v) = radius x ^ 2 * v ^ 2 := by ring
        _ = (x ⬝ᵥ x) * v ^ 2 := by rw [hr2]
    rw [hcross, hsq1, hsq2, hX2] at hi
    have hi2 : (x ⬝ᵥ x) * (v₁ ⬝ᵥ v₂) = (x ⬝ᵥ x) * (v ^ 2 * Real.cos i) := by
      calc (x ⬝ᵥ x) * (v₁ ⬝ᵥ v₂) = Real.cos i * ((x ⬝ᵥ x) * v ^ 2) := hi
        _ = (x ⬝ᵥ x) * (v ^ 2 * Real.cos i) := by ring
    exact mul_left_cancel₀ (ne_of_gt hXpos) hi2
  have hsub := speedSq_sub_of_speedSq_eq hv₁ hv₂ hdot
  unfold impulseMagnitude
  rw [hsub]
  exact sqrt_two_mul_sq_mul_one_sub_cos hv.le hi₀ hiπ

end OrbitalPorts
