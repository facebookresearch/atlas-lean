/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.CrossProduct

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Orbital ports: energy-defined vis-viva and one tangential impulse

## i. Overview

A state of relative two-body motion is a position `x` and a velocity `v` in `Fin 3 → ℝ`,
relative to the attracting center at the origin of a fixed inertial frame, with gravitational
parameter `μ = G (m₁ + m₂) > 0`. Its specific energy is `E = |v|² / 2 - μ / r`, `r = |x|`, and
for `E < 0` the energy-defined semi-major axis is `a = -μ / (2 E)`. Then `a > 0`, and for a
collision-free state (`r > 0`) the vis-viva identity `|v|² = μ (2 / r - 1 / a)` holds.

The Euclidean squares are dot products, `|v|² = v ⬝ᵥ v`: the default norm on `Fin 3 → ℝ` is the
sup norm and is not used. Angular momentum is the cross product `x ⨯₃ v`.

A tangential impulse of signed magnitude `Δv` changes the velocity along the flight direction,
`v' = v + (Δv / |v|) • v`, at the fixed position; the post-impulse speed is `|v| + Δv` in
square, the orbital plane is unchanged, and vis-viva applied to the new state gives the new
semi-major axis.

These are identities about one fixed state, not about a trajectory. No solution of the
two-body equation is constructed, no elliptic trajectory is asserted (a state with `E < 0` and
zero angular momentum is radial), and no transfer cost or two-impulse optimality is claimed. At
`E = 0` the formula `-μ / (2 E)` returns Lean's junk value `0`, not a finite semi-major axis.
Each result assumes only the hypotheses its proof uses.

## ii. Key results

- `OrbitalPorts.visViva`: `|v|² = μ (2 / r - 1 / a)` for `μ, r > 0`, `E < 0`.
- `OrbitalPorts.semiMajorAxis_pos`: `a > 0` follows from `μ > 0`, `E < 0`.
- `OrbitalPorts.visViva_tangentialImpulse`: the identity after one tangential impulse.
- `OrbitalPorts.semiMajorAxis_tangentialImpulse_eq_radius_iff`: one impulse from a circular
  state keeps `a = r` only if it keeps the speed.

## iii. Table of contents

- A. State energy and vis-viva
- B. One tangential impulse

## iv. References

- H. D. Curtis, *Orbital Mechanics for Engineering Students*, ch. 2: specific energy,
  `a = -μ / (2 ε)` and the vis-viva equation.
- R. R. Bate, D. D. Mueller and J. E. White, *Fundamentals of Astrodynamics*, ch. 1-2.
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

/-- A circular state, `|v|² = μ / r` with `μ, r > 0`, has `E = -μ / (2 r)` and `a = r`. -/
lemma semiMajorAxis_of_circular {μ : ℝ} {x v : Fin 3 → ℝ} (hμ : 0 < μ) (hr : 0 < radius x)
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

/-- A tangential impulse rescales the angular momentum `x ⨯₃ v` by `1 + Δv / |v|`: the orbital
plane is unchanged. -/
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

/-- From a circular state, `|v|² = μ / r`, a tangential impulse with negative post-impulse
energy keeps `a' = r` only if it keeps the speed (`Δv = 0`) or reverses the velocity
(`Δv = -2 |v|`). So one impulse does not move a circular state onto a circle of another radius;
no transfer cost or optimality is claimed. -/
lemma semiMajorAxis_tangentialImpulse_eq_radius_iff {μ Δv : ℝ} {x v : Fin 3 → ℝ}
    (hμ : 0 < μ) (hr : 0 < radius x) (hcirc : speedSq v = μ / radius x)
    (hE : specificEnergy μ x (tangentialImpulse v Δv) < 0) :
    semiMajorAxis μ x (tangentialImpulse v Δv) = radius x ↔
      Δv = 0 ∨ Δv = -2 * Real.sqrt (speedSq v) := by
  have hs_pos : 0 < speedSq v := by rw [hcirc]; exact div_pos hμ hr
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
      rw [hS_eq, ← hcirc, hsq]
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
      rw [ht2, hsq, hcirc]
    rw [hS_eq] at h2
    have hdiv : 1 / semiMajorAxis μ x (tangentialImpulse v Δv) = 1 / radius x := by
      field_simp at h2 ⊢
      linear_combination h2
    field_simp at hdiv
    exact hdiv.symm

end OrbitalPorts
