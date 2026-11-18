/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.Real.Basic
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
`Mechanics.EulerBernoulli.beamStiffness_quad_form`.

## ii. Key results

- `Mechanics.EulerBernoulli.beamStiffness_transpose`: symmetry.
- `Mechanics.EulerBernoulli.beamStiffness_mulVec_translation`
  and `Mechanics.EulerBernoulli.beamStiffness_mulVec_rotation`:
  rigid-body kernel vectors.
- `Mechanics.EulerBernoulli.beamStiffness_quad_form`: the
  energy quadratic form.

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

end Mechanics.EulerBernoulli
