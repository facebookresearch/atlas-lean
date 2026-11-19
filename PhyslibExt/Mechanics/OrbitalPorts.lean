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
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Orbital ports: energy-defined vis-viva, one tangential impulse and circular orbits

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

## iii. Table of contents

- A. State energy and vis-viva
- B. One tangential impulse
- C. The circular-orbit premises
- D. Speed and period
- E. Units
- F. Planar to spatial state

## iv. References

- H. D. Curtis, *Orbital Mechanics for Engineering Students*, ch. 2: specific energy,
  `a = -μ / (2 ε)`, the vis-viva equation and circular orbits (`v = √(μ / r)`,
  `T = 2 π r ^ (3 / 2) / √μ`).
- R. R. Bate, D. D. Mueller and J. E. White, *Fundamentals of Astrodynamics*, ch. 1-2.
- D. A. Vallado, *Fundamentals of Astrodynamics and Applications*, ch. 1-2: the two-body
  equation `r'' = -μ r / r ^ 3` and the orbital plane.
- Physlib, `PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Circular`: the
  circular orbits whose conclusions are the premises of section C.
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

end OrbitalPorts
