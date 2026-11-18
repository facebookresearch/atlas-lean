/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Beam element stiffness matrix

## i. Overview

The classical prismatic Euler-Bernoulli beam element stiffness
matrix in nodal coordinates `(v1, θ1, v2, θ2)`, with flexural
rigidity `EI` and length `L`: `K = (EI / L^3)` times the coefficient
matrix with rows `(12, 6L, -12, 6L)`, `(6L, 4L^2, -6L, 2L^2)`,
`(-12, -6L, 12, -6L)`, `(6L, 2L^2, -6L, 4L^2)`. The matrix is
symmetric; rigid translation and rigid rotation are in its
kernel; and its quadratic form `d ⬝ᵥ (K *ᵥ d)` (twice the strain
energy) has the closed form recorded in
`Mechanics.EulerBernoulli.beamStiffness_quad_form`. The same
quadratic form factors into two squares, which gives positive
semidefiniteness for `EI > 0`, `L > 0` and identifies the kernel
with the rigid-motion span.

## ii. Key results

- `Mechanics.EulerBernoulli.beamStiffness_transpose`: symmetry.
- `Mechanics.EulerBernoulli.beamStiffness_mulVec_translation`
  and `Mechanics.EulerBernoulli.beamStiffness_mulVec_rotation`:
  rigid-body kernel vectors.
- `Mechanics.EulerBernoulli.beamStiffness_quad_form`: the
  energy quadratic form.
- `Mechanics.EulerBernoulli.beamStiffness_quad_form_factor`:
  the two-square factorization of that form.
- `Mechanics.EulerBernoulli.beamStiffness_posSemidef`:
  positive semidefiniteness for positive rigidity and length.
- `Mechanics.EulerBernoulli.beamStiffness_mulVec_eq_zero_iff`:
  the kernel is exactly the rigid-motion span.

## iii. Table of contents

- A. The stiffness matrix and its energy

## iv. References

- K.-J. Bathe, *Finite Element Procedures*, 2nd edition,
  Prentice-Hall, 2014, Section 5.2 (beam element stiffness
  matrix in the nodal coordinates (v1, θ1, v2, θ2) with
  conjugate end forces).
- R. D. Cook, D. S. Malkus, M. E. Plesha and R. J. Witt,
  *Concepts and Applications of Finite Element Analysis*,
  4th edition, Wiley, 2002, Section 2.5 (beam element).
-/

@[expose] public section

open Matrix

/-! ## A. The stiffness matrix and its energy -/
namespace Mechanics.EulerBernoulli


/-- Beam-element stiffness matrix for a prismatic Euler-Bernoulli
element with flexural rigidity `EI` and length `L`, in the nodal
coordinates `(v1, θ1, v2, θ2)` (deflections and rotations at the
two ends), with the conjugate end-force sign convention:
`K = (EI / L^3)` times the classical coefficient matrix. The
definition is the totalized formula; no positivity is asserted by
the definition itself. -/
noncomputable def beamStiffness (EI L : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (EI / L ^ 3) • !![12, 6 * L, -12, 6 * L;
    6 * L, 4 * L ^ 2, -6 * L, 2 * L ^ 2;
    -12, -6 * L, 12, -6 * L;
    6 * L, 2 * L ^ 2, -6 * L, 4 * L ^ 2]

/-- The beam stiffness matrix is symmetric. -/
theorem beamStiffness_transpose (EI L : ℝ) :
    (beamStiffness EI L)ᵀ = beamStiffness EI L := by
  unfold beamStiffness
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

/-- Rigid translation is in the kernel: `(1, 0, 1, 0)` produces
no end forces. -/
theorem beamStiffness_mulVec_translation (EI L : ℝ) :
    beamStiffness EI L *ᵥ ![1, 0, 1, 0] = 0 := by
  unfold beamStiffness
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Rigid rotation is in the kernel: `(0, 1, L, 1)` (the linear
deflection field `v(x) = x`) produces no end forces. -/
theorem beamStiffness_mulVec_rotation (EI L : ℝ) :
    beamStiffness EI L *ᵥ ![0, 1, L, 1] = 0 := by
  unfold beamStiffness
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- Curvature energy as a quadratic form: `d ⬝ᵥ (K *ᵥ d)` (twice
the strain energy) equals
`(EI / L^3) * (12 * (v1 - v2)^2 + 12 * L * (v1 - v2) * (θ1 + θ2)
+ 4 * L^2 * (θ1^2 + θ1 * θ2 + θ2^2))`. -/
theorem beamStiffness_quad_form (EI L : ℝ) (d : Fin 4 → ℝ) :
    d ⬝ᵥ (beamStiffness EI L *ᵥ d)
      = (EI / L ^ 3) * (12 * (d 0 - d 2) ^ 2
        + 12 * L * (d 0 - d 2) * (d 1 + d 3)
        + 4 * L ^ 2 * ((d 1) ^ 2 + d 1 * d 3 + (d 3) ^ 2)) := by
  unfold beamStiffness
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- The beam-stiffness quadratic form factors into two squares:
with end data `d = (v1, θ1, v2, θ2)`, twice the strain energy is
`(EI / L^3)` times
`12 * ((v1 - v2) + (L / 2) * (θ1 + θ2))^2 + L^2 * (θ1 - θ2)^2`. -/
theorem beamStiffness_quad_form_factor (EI L : ℝ) (d : Fin 4 → ℝ) :
    d ⬝ᵥ (beamStiffness EI L *ᵥ d)
      = (EI / L ^ 3) * (12 * ((d 0 - d 2) + (L / 2) * (d 1 + d 3)) ^ 2
        + L ^ 2 * (d 1 - d 3) ^ 2) := by
  unfold beamStiffness
  simp [dotProduct, mulVec, Fin.sum_univ_four]
  ring

/-- For positive flexural rigidity and positive length, the
beam-element stiffness matrix is positive semidefinite. -/
theorem beamStiffness_posSemidef {EI L : ℝ} (hEI : 0 < EI)
    (hL : 0 < L) :
    (beamStiffness EI L).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [beamStiffness]
  · intro x
    have hstar : star x = x := by simp
    rw [hstar, beamStiffness_quad_form_factor]
    have hc : 0 ≤ EI / L ^ 3 := by positivity
    have hsq : 0 ≤ 12 * ((x 0 - x 2) + (L / 2) * (x 1 + x 3)) ^ 2
        + L ^ 2 * (x 1 - x 3) ^ 2 := by positivity
    exact mul_nonneg hc hsq

/-- For positive flexural rigidity and positive length, the
kernel of the beam-element stiffness matrix is exactly the span
of rigid translation `(1, 0, 1, 0)` and rigid rotation
`(0, 1, L, 1)`. -/
theorem beamStiffness_mulVec_eq_zero_iff {EI L : ℝ} (hEI : 0 < EI)
    (hL : 0 < L) (d : Fin 4 → ℝ) :
    beamStiffness EI L *ᵥ d = 0
      ↔ ∃ a b : ℝ, d = a • ![1, 0, 1, 0] + b • ![0, 1, L, 1] := by
  constructor
  · intro h
    have hdot : d ⬝ᵥ (beamStiffness EI L *ᵥ d) = 0 := by
      rw [h]
      exact dotProduct_zero d
    rw [beamStiffness_quad_form_factor] at hdot
    have hc : (0:ℝ) < EI / L ^ 3 := by positivity
    have hS := (mul_eq_zero.mp hdot).resolve_left (ne_of_gt hc)
    have h1 : 0 ≤ 12 * ((d 0 - d 2) + (L / 2) * (d 1 + d 3)) ^ 2 := by positivity
    have h2 : 0 ≤ L ^ 2 * (d 1 - d 3) ^ 2 := by positivity
    rw [add_eq_zero_iff_of_nonneg h1 h2] at hS
    obtain ⟨hS1, hS2⟩ := hS
    have ha : (d 0 - d 2) + (L / 2) * (d 1 + d 3) = 0 := by
      have hsq : ((d 0 - d 2) + (L / 2) * (d 1 + d 3)) ^ 2 = 0 :=
        (mul_eq_zero.mp hS1).resolve_left (by norm_num)
      exact sq_eq_zero_iff.mp hsq
    have hb : d 1 - d 3 = 0 := by
      have hsq : (d 1 - d 3) ^ 2 = 0 :=
        (mul_eq_zero.mp hS2).resolve_left (pow_ne_zero 2 (ne_of_gt hL))
      exact sq_eq_zero_iff.mp hsq
    have hd3 : d 3 = d 1 := by linarith
    rw [hd3] at ha
    have hd2 : d 2 = d 0 + d 1 * L := by
      have hLL : L / 2 * (d 1 + d 1) = d 1 * L := by ring
      rw [hLL] at ha
      linarith
    refine ⟨d 0, d 1, ?_⟩
    funext i
    fin_cases i
    · simp
    · simp
    · simp [hd2]
    · simp [hd3]
  · rintro ⟨a, b, rfl⟩
    have h0 : (!![12, 6 * L, -12, 6 * L;
        6 * L, 4 * L ^ 2, -6 * L, 2 * L ^ 2;
        -12, -6 * L, 12, -6 * L;
        6 * L, 2 * L ^ 2, -6 * L, 4 * L ^ 2] : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ
        (a • ![1, 0, 1, 0] + b • ![0, 1, L, 1]) = 0 := by
      ext i
      fin_cases i <;> simp [mulVec] <;> ring
    simp only [beamStiffness, Matrix.smul_mulVec, h0, smul_zero]
end Mechanics.EulerBernoulli
