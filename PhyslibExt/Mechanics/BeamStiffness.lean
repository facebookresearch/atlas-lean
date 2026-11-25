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
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import PhyslibExt.Mechanics.HermiteConsistentLoads
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
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
with the rigid-motion span. Combining this bending block with
the two-node axial block gives the six-DOF local frame matrix in
`(u1, v1, θ1, u2, v2, θ2)` order; axial and bending energies
add, and its kernel is the three planar rigid modes. For a
quartic deflection field satisfying `EI * iteratedDeriv 4 y = w`,
the conjugate end-force vector is `K` applied to the end data
minus the uniform consistent load vector, whose entries are the
Hermite consistent-load integrals.

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
- `Mechanics.EulerBernoulli.frameStiffness_quad_form_factor`
  and `Mechanics.EulerBernoulli.frameStiffness_energy_add`:
  the six-DOF local frame energy as axial plus bending squares.
- `Mechanics.EulerBernoulli.frameStiffness_posSemidef` and
  `Mechanics.EulerBernoulli.frameStiffness_mulVec_eq_zero_iff`:
  frame positivity and the three planar rigid modes.
- `Mechanics.EulerBernoulli.uniformLoadVector_entries_hermite`:
  the load-vector entries as Hermite consistent-load integrals.
- `Mechanics.EulerBernoulli.quartic_end_force_identity`: the
  uniform-load quartic end-force identity.

## iii. Table of contents

- A. The stiffness matrix and its energy
- B. Six-DOF local frame block
- C. Uniform-load end forces

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

open Matrix intervalIntegral

/-! ## A. The stiffness matrix and its energy -/
namespace Mechanics.EulerBernoulli


/-- Beam-element stiffness matrix for a prismatic Euler-Bernoulli element with flexural rigidity
`EI` and length `L`, in the nodal coordinates `(v1, θ1, v2, θ2)` (deflections and rotations at the
two ends), with the conjugate end-force sign convention: `K = (EI / L^3)` times the classical
coefficient matrix. The definition is the totalized formula; no positivity is asserted by the
definition itself. At `L = 0` it is the zero matrix (`x / 0 = 0`). -/
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
the strain energy) equals `(EI / L^3) * Q` with
`Q = 12 * (v1 - v2)^2 + 12 * L * (v1 - v2) * (θ1 + θ2) + 4 * L^2 * (θ1^2 + θ1 * θ2 + θ2^2)`.
At `L = 0` both sides are `0` (`x / 0 = 0`). -/
theorem beamStiffness_quad_form (EI L : ℝ) (d : Fin 4 → ℝ) :
    d ⬝ᵥ (beamStiffness EI L *ᵥ d)
      = (EI / L ^ 3) * (12 * (d 0 - d 2) ^ 2
        + 12 * L * (d 0 - d 2) * (d 1 + d 3)
        + 4 * L ^ 2 * ((d 1) ^ 2 + d 1 * d 3 + (d 3) ^ 2)) := by
  unfold beamStiffness
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- The beam-stiffness quadratic form factors into two squares: with end data
`d = (v1, θ1, v2, θ2)`, twice the strain energy is `(EI / L^3)` times
`12 * ((v1 - v2) + (L / 2) * (θ1 + θ2))^2 + L^2 * (θ1 - θ2)^2`. At `L = 0` both sides are `0`
(`x / 0 = 0`). -/
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

/-! ## B. Six-DOF local frame block -/

/-- Two-node axial stiffness matrix with axial rigidity `EA` and length `L`, in coordinates
`(u1, u2)`: `(EA / L) * [[1, -1], [-1, 1]]`. The definition is the totalized formula: at `L = 0` it
is the zero matrix. -/
noncomputable def axialStiffness (EA L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (EA / L) • !![1, -1; -1, 1]

/-- Six-DOF local frame-element stiffness matrix, in the fixed ordering `(u1, v1, θ1, u2, v2, θ2)`:
axial displacement, transverse deflection, and rotation at end 1, then the same three coordinates at
end 2. It combines the axial block `axialStiffness` on `(u1, u2)` with the bending block
`beamStiffness` on `(v1, θ1, v2, θ2)`, with no axial-bending coupling. The definition is the
totalized formula: at `L = 0` it is the zero matrix. -/
noncomputable def frameStiffness (EA EI L : ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  !![EA / L, 0, 0, -EA / L, 0, 0;
    0, 12 * EI / L ^ 3, 6 * EI / L ^ 2, 0,
      -12 * EI / L ^ 3, 6 * EI / L ^ 2;
    0, 6 * EI / L ^ 2, 4 * EI / L, 0,
      -6 * EI / L ^ 2, 2 * EI / L;
    -EA / L, 0, 0, EA / L, 0, 0;
    0, -12 * EI / L ^ 3, -6 * EI / L ^ 2, 0,
      12 * EI / L ^ 3, -6 * EI / L ^ 2;
    0, 6 * EI / L ^ 2, 2 * EI / L, 0,
      -6 * EI / L ^ 2, 4 * EI / L]

/-- The frame-element quadratic form (twice the strain energy)
factors as the axial square `(EA / L) * (u2 - u1)^2` plus the two bending squares
`(EI / L^3) * (12 * ((v1 - v2) + (L / 2) * (θ1 + θ2))^2 + L^2 * (θ1 - θ2)^2)`.
At `L = 0` both sides are `0` (`x / 0 = 0`). -/
theorem frameStiffness_quad_form_factor (EA EI L : ℝ)
    (d : Fin 6 → ℝ) :
    d ⬝ᵥ (frameStiffness EA EI L *ᵥ d)
      = (EA / L) * (d 3 - d 0) ^ 2
        + (EI / L ^ 3) * (12 * ((d 1 - d 4)
            + (L / 2) * (d 2 + d 5)) ^ 2
          + L ^ 2 * (d 2 - d 5) ^ 2) := by
  by_cases hL : L = 0
  · subst hL
    simp only [frameStiffness, dotProduct, Matrix.mulVec, Fin.sum_univ_six,
      Matrix.of_apply, Fin.isValue, Matrix.cons_val]
    ring
  · have hL' : L ≠ 0 := hL
    simp only [frameStiffness, dotProduct, Matrix.mulVec, Fin.sum_univ_six,
      Matrix.of_apply, Fin.isValue, Matrix.cons_val]
    field_simp
    ring

/-- Axial and bending energies add: the frame quadratic form is
the axial quadratic form in `(u1, u2)` plus the bending quadratic
form in `(v1, θ1, v2, θ2)`. -/
theorem frameStiffness_energy_add (EA EI L : ℝ)
    (d : Fin 6 → ℝ) :
    d ⬝ᵥ (frameStiffness EA EI L *ᵥ d)
      = (![d 0, d 3] : Fin 2 → ℝ)
          ⬝ᵥ (axialStiffness EA L *ᵥ ![d 0, d 3])
        + (![d 1, d 2, d 4, d 5] : Fin 4 → ℝ)
          ⬝ᵥ (beamStiffness EI L *ᵥ ![d 1, d 2, d 4, d 5]) := by
  by_cases hL : L = 0
  · subst hL
    simp only [frameStiffness, axialStiffness, beamStiffness, dotProduct,
      Matrix.mulVec, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_six,
      Matrix.of_apply, Fin.isValue, Matrix.cons_val, Matrix.smul_apply, smul_eq_mul]
    ring
  · have hL' : L ≠ 0 := hL
    simp only [frameStiffness, axialStiffness, beamStiffness, dotProduct,
      Matrix.mulVec, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_six,
      Matrix.of_apply, Fin.isValue, Matrix.cons_val, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- The frame-element stiffness matrix is symmetric. -/
theorem frameStiffness_transpose (EA EI L : ℝ) :
    (frameStiffness EA EI L)ᵀ = frameStiffness EA EI L := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- For positive axial rigidity, flexural rigidity, and length,
the frame-element stiffness matrix is positive semidefinite. -/
theorem frameStiffness_posSemidef {EA EI L : ℝ} (hEA : 0 < EA)
    (hEI : 0 < EI) (hL : 0 < L) :
    (frameStiffness EA EI L).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr
      (frameStiffness_transpose EA EI L)
  · intro x
    have h := frameStiffness_quad_form_factor EA EI L x
    have hsx : star x = x := by simp
    rw [hsx, h]
    positivity

/-- For positive axial rigidity, flexural rigidity, and length,
the kernel of the frame-element stiffness matrix is exactly the
span of the three planar rigid modes in the ordering
`(u1, v1, θ1, u2, v2, θ2)`: axial translation
`(1, 0, 0, 1, 0, 0)`, transverse translation
`(0, 1, 0, 0, 1, 0)`, and rigid rotation
`(0, 0, 1, 0, L, 1)`. -/
theorem frameStiffness_mulVec_eq_zero_iff {EA EI L : ℝ}
    (hEA : 0 < EA) (hEI : 0 < EI) (hL : 0 < L)
    (d : Fin 6 → ℝ) :
    frameStiffness EA EI L *ᵥ d = 0
      ↔ ∃ a b c : ℝ,
        d = a • ![1, 0, 0, 1, 0, 0]
          + b • ![0, 1, 0, 0, 1, 0]
          + c • ![0, 0, 1, 0, L, 1] := by
  constructor
  · intro hKd
    have hL' : L ≠ 0 := hL.ne'
    have hdot : d ⬝ᵥ (frameStiffness EA EI L *ᵥ d) = 0 := by
      rw [hKd]
      exact dotProduct_zero _
    have hfact := frameStiffness_quad_form_factor EA EI L d
    rw [hdot] at hfact
    have hEAL : 0 < EA / L := div_pos hEA hL
    have hEIL : 0 < EI / L ^ 3 := div_pos hEI (pow_pos hL 3)
    have haxnn : 0 ≤ (EA / L) * (d 3 - d 0) ^ 2 :=
      mul_nonneg (le_of_lt hEAL) (sq_nonneg _)
    have hbenn : 0 ≤ (EI / L ^ 3) * (12 * ((d 1 - d 4)
          + (L / 2) * (d 2 + d 5)) ^ 2 + L ^ 2 * (d 2 - d 5) ^ 2) :=
      mul_nonneg (le_of_lt hEIL) (add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    obtain ⟨hax, hben⟩ := (add_eq_zero_iff_of_nonneg haxnn hbenn).mp hfact.symm
    have h10 : d 3 - d 0 = 0 := by
      have hsq : (d 3 - d 0) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hax with h | h
        · exact absurd h hEAL.ne'
        · exact h
      exact sq_eq_zero_iff.mp hsq
    have hSS : 12 * ((d 1 - d 4) + (L / 2) * (d 2 + d 5)) ^ 2
        + L ^ 2 * (d 2 - d 5) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hben with h | h
      · exact absurd h hEIL.ne'
      · exact h
    have hSnn : 0 ≤ 12 * ((d 1 - d 4) + (L / 2) * (d 2 + d 5)) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hTnn : 0 ≤ L ^ 2 * (d 2 - d 5) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    obtain ⟨hS0, hT0⟩ := (add_eq_zero_iff_of_nonneg hSnn hTnn).mp hSS
    have hS : (d 1 - d 4) + (L / 2) * (d 2 + d 5) = 0 := by
      have hsq : ((d 1 - d 4) + (L / 2) * (d 2 + d 5)) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hS0 with h | h
        · norm_num at h
        · exact h
      exact sq_eq_zero_iff.mp hsq
    have hT : d 2 - d 5 = 0 := by
      have hsq : (d 2 - d 5) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hT0 with h | h
        · exact absurd h (pow_pos hL 2).ne'
        · exact h
      exact sq_eq_zero_iff.mp hsq
    have h30 : d 3 = d 0 := by linarith
    have h52 : d 5 = d 2 := by linarith
    have h41 : d 4 = d 1 + L * d 2 := by
      rw [h52] at hS
      have h2 : (L / 2) * (d 2 + d 2) = L * d 2 := by ring
      rw [h2] at hS
      linarith
    have h41' : d 4 = d 1 + d 2 * L := by
      rw [mul_comm (d 2) L]
      exact h41
    refine ⟨d 0, d 1, d 2, ?_⟩
    funext i
    fin_cases i
    · simp only [Fin.reduceFinMk]
      simp only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val,
        smul_eq_mul]
      ring
    · simp only [Fin.reduceFinMk]
      simp only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val,
        smul_eq_mul]
      ring
    · simp only [Fin.reduceFinMk]
      simp only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val,
        smul_eq_mul]
      ring
    · simp only [Fin.reduceFinMk]
      simp only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val,
        smul_eq_mul]
      rw [h30]
      ring
    · simp only [Fin.reduceFinMk]
      simp only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val,
        smul_eq_mul]
      rw [h41']
      ring
    · simp only [Fin.reduceFinMk]
      simp only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val,
        smul_eq_mul]
      rw [h52]
      ring
  · rintro ⟨a, b, c, rfl⟩
    have hL' : L ≠ 0 := hL.ne'
    ext i
    fin_cases i <;>
      simp only [Fin.reduceFinMk] <;>
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_six, frameStiffness,
        Matrix.of_apply, Fin.isValue, Matrix.cons_val, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] <;>
      field_simp <;>
      ring
/-! ## C. Uniform-load end forces -/

/-- Consistent load vector for constant load `w` on the beam
element, in the nodal order `(v1, θ1, v2, θ2)`:
`(w * L / 2, w * L^2 / 12, w * L / 2, -w * L^2 / 12)`. -/
noncomputable def uniformLoadVector (w L : ℝ) : Fin 4 → ℝ :=
  ![w * L / 2, w * L ^ 2 / 12, w * L / 2, -w * L ^ 2 / 12]

/-- The four entries of `uniformLoadVector` are the Hermite
consistent-load integrals for the unit end-data Hermite shape
functions, in the same interleaved nodal order
`(v1, θ1, v2, θ2)`. -/
lemma uniformLoadVector_entries_hermite {w L : ℝ} (hL : L ≠ 0) :
    (∫ x in (0 : ℝ)..L, w * HermiteCubic.hermite L 1 0 0 0 x
      = uniformLoadVector w L 0)
    ∧ (∫ x in (0 : ℝ)..L, w * HermiteCubic.hermite L 0 1 0 0 x
      = uniformLoadVector w L 1)
    ∧ (∫ x in (0 : ℝ)..L, w * HermiteCubic.hermite L 0 0 1 0 x
      = uniformLoadVector w L 2)
    ∧ (∫ x in (0 : ℝ)..L, w * HermiteCubic.hermite L 0 0 0 1 x
      = uniformLoadVector w L 3) := by
  have h := HermiteCubic.hermite_consistent_loads_hermite hL (w := w)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [uniformLoadVector] using h.1
  · simpa [uniformLoadVector] using h.2.1
  · simpa [uniformLoadVector] using h.2.2.1
  · simpa [uniformLoadVector] using h.2.2.2

/-- End data `(y(0), y'(0), y(L), y'(L))` of a deflection field `y` on the element `[0, L]`.
Derivatives are `0` where `y` is not differentiable. -/
noncomputable def beamEndData (L : ℝ) (y : ℝ → ℝ) : Fin 4 → ℝ :=
  ![y 0, iteratedDeriv 1 y 0, y L, iteratedDeriv 1 y L]

/-- Conjugate end-force vector of a deflection field `y`, in the nodal order `(v1, θ1, v2, θ2)`, for
the sign conventions `M = -EI * y''` and `V = M' = -EI * y'''`:
`(EI * y'''(0), -EI * y''(0), -EI * y'''(L), EI * y''(L))`, i.e. `(-V(0), M(0), V(L), -M(L))`.
Derivatives are `0` where the function is not differentiable. -/
noncomputable def beamEndForces (EI L : ℝ) (y : ℝ → ℝ) :
    Fin 4 → ℝ :=
  ![EI * iteratedDeriv 3 y 0, -EI * iteratedDeriv 2 y 0,
    -EI * iteratedDeriv 3 y L, EI * iteratedDeriv 2 y L]

/-- Uniform-load quartic end-force identity.

For a quartic deflection field
`y(x) = a + b*x + c*x^2 + d*x^3 + e*x^4` satisfying
`EI * y'''' = w` on the element `[0, L]` (`EI > 0`, `L > 0`),
the conjugate end-force vector is the stiffness action on the
end data minus the uniform consistent load vector. -/
theorem quartic_end_force_identity {EI L w : ℝ}
    (hEI : 0 < EI) (hL : 0 < L) {y : ℝ → ℝ}
    {a b c d e : ℝ}
    (hy : ∀ x : ℝ,
      y x = a + b * x + c * x ^ 2 + d * x ^ 3 + e * x ^ 4)
    (hload : ∀ x ∈ Set.Icc 0 L,
      EI * iteratedDeriv 4 y x = w) :
    beamEndForces EI L y
      = beamStiffness EI L *ᵥ beamEndData L y
        - uniformLoadVector w L := by
  have hyfun : y = fun x => a + b * x ^ 1 + c * x ^ 2 + d * x ^ 3 + e * x ^ 4 := by
    funext x
    simp only [hy x, pow_one]
  have d1 : ∀ x : ℝ, iteratedDeriv 1 y x
      = b + 2 * c * x + 3 * d * x ^ 2 + 4 * e * x ^ 3 := by
    intro x
    rw [hyfun]
    simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field,
      iteratedDeriv_pow, iteratedDeriv_const]
    simp only [show Nat.descFactorial 1 1 = 1 from by decide,
      show Nat.descFactorial 2 1 = 2 from by decide,
      show Nat.descFactorial 3 1 = 3 from by decide,
      show Nat.descFactorial 4 1 = 4 from by decide]
    simp
    ring
  have d2 : ∀ x : ℝ, iteratedDeriv 2 y x
      = 2 * c + 6 * d * x + 12 * e * x ^ 2 := by
    intro x
    rw [hyfun]
    simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field,
      iteratedDeriv_pow, iteratedDeriv_const]
    simp only [show Nat.descFactorial 1 2 = 0 from by decide,
      show Nat.descFactorial 2 2 = 2 from by decide,
      show Nat.descFactorial 3 2 = 6 from by decide,
      show Nat.descFactorial 4 2 = 12 from by decide]
    simp
    ring
  have d3 : ∀ x : ℝ, iteratedDeriv 3 y x = 6 * d + 24 * e * x := by
    intro x
    rw [hyfun]
    simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field,
      iteratedDeriv_pow, iteratedDeriv_const]
    simp only [show Nat.descFactorial 1 3 = 0 from by decide,
      show Nat.descFactorial 2 3 = 0 from by decide,
      show Nat.descFactorial 3 3 = 6 from by decide,
      show Nat.descFactorial 4 3 = 24 from by decide]
    simp
    ring
  have d4 : ∀ x : ℝ, iteratedDeriv 4 y x = 24 * e := by
    intro x
    rw [hyfun]
    simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field,
      iteratedDeriv_pow, iteratedDeriv_const]
    simp only [show Nat.descFactorial 1 4 = 0 from by decide,
      show Nat.descFactorial 2 4 = 0 from by decide,
      show Nat.descFactorial 3 4 = 0 from by decide,
      show Nat.descFactorial 4 4 = 24 from by decide]
    simp
    ring
  have hLne : L ≠ 0 := ne_of_gt hL
  have hw : w = 24 * EI * e := by
    have h := hload 0 ⟨le_rfl, hL.le⟩
    rw [d4] at h
    linarith
  have e_y0 : y 0 = a := by rw [hy]; ring
  have e_d10 : iteratedDeriv 1 y 0 = b := by rw [d1]; ring
  have e_d20 : iteratedDeriv 2 y 0 = 2 * c := by rw [d2]; ring
  have e_d30 : iteratedDeriv 3 y 0 = 6 * d := by rw [d3]; ring
  ext i
  fin_cases i <;>
    simp [beamEndForces, beamEndData, beamStiffness, uniformLoadVector,
      e_y0, hy L, d1 L, d2 L, d3 L, e_d10, e_d20, e_d30, hw] <;>
    field_simp <;>
    ring
end Mechanics.EulerBernoulli
