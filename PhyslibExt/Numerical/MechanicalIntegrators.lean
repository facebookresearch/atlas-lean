/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Mechanical integrators: symplectic versus explicit Euler

## i. Overview

One-step matrices for the harmonic oscillator with mass `m`, stiffness
`k`, and step `h`, in `(q, p)` coordinates over `Fin 2`. The
momentum-first (symplectic Euler) step is symplectic for the concrete
alternating matrix `J = [[0, -1], [1, 0]]` (the `Fin 1 ⊕ Fin 1`
`Matrix.J` under the standard identification) and has determinant `1`;
the explicit Euler step has determinant `1 + h^2 * k / m`. Symplecticity
does not imply exact oscillator-energy preservation, as the concrete
counterexample at `m = k = h = 1` shows. No general integrator theorem
is claimed.

## ii. Key results

- `MechanicalIntegrators.symplecticEulerMatrix_transpose_mul`: the
  transposed symplectic identity `Mᵀ * J * M = J` for the concrete
  step matrix.
- `MechanicalIntegrators.symplecticEuler_energy_not_preserved`:
  at `m = k = h = 1` the step sends `(q, p) = (0, 1)` to `(1, 1)`,
  changing the oscillator energy from `1 / 2` to `1`.

## iii. Table of contents

- A. The two Euler step matrices

## iv. References

- `Matrix.J` and `SymplecticGroup.mem_iff'` in Mathlib's
  `Mathlib.LinearAlgebra.SymplecticGroup`, whose transposed identity
  is realized here in `Fin 2` coordinates.

## A. The two Euler step matrices

-/

@[expose] public section

namespace MechanicalIntegrators

/-- The momentum-first (symplectic Euler) step matrix for the harmonic
oscillator with mass `m`, stiffness `k`, and step `h`, acting on the
state `(q, p)`: `p' = p - h * k * q`, `q' = q + h * p' / m`, so
`M = [[1 - h^2 * k / m, h / m], [-h * k, 1]]` in `(q, p)` coordinates,
written with `Matrix.of` over `Fin 2`. -/
noncomputable def symplecticEulerMatrix (m k h : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1 - h ^ 2 * k / m, h / m], ![-h * k, 1]]

/-- The explicit Euler step matrix for the same oscillator:
`q' = q + h * p / m`, `p' = p - h * k * q`. -/
noncomputable def explicitEulerMatrix (m k h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, h / m], ![-h * k, 1]]

/-- Oscillator energy of the state `(q, p)`: `p^2 / (2m) + k q^2 / 2`. -/
noncomputable def oscillatorEnergy (m k : ℝ) (state : Fin 2 → ℝ) : ℝ :=
  state 1 ^ 2 / (2 * m) + k * state 0 ^ 2 / 2

/-- The symplectic Euler matrix has determinant `1` for every real
`m ≠ 0`, `k`, `h`. -/
lemma symplecticEulerMatrix_det {m k h : ℝ} (hm : m ≠ 0) :
    (symplecticEulerMatrix m k h).det = 1 := by
  simp [symplecticEulerMatrix, Matrix.det_fin_two, Matrix.of_apply]
  field_simp
  ring

/-- The explicit Euler matrix has determinant `1 + h^2 * k / m`: it
expands phase volume whenever `h^2 * k / m > 0`. -/
lemma explicitEulerMatrix_det {m k h : ℝ} (hm : m ≠ 0) :
    (explicitEulerMatrix m k h).det = 1 + h ^ 2 * k / m := by
  simp [explicitEulerMatrix, Matrix.det_fin_two, Matrix.of_apply]
  field_simp

/-- Symplecticity of the momentum-first step in transposed form:
`Mᵀ * J * M = J` for the concrete `Fin 2` alternating matrix
`J = [[0, -1], [1, 0]]`. -/
lemma symplecticEulerMatrix_transpose_mul {m k h : ℝ} (hm : m ≠ 0) :
    (symplecticEulerMatrix m k h).transpose *
        Matrix.of ![![0, -1], ![1, 0]] * symplecticEulerMatrix m k h =
      Matrix.of ![![0, -1], ![1, 0]] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticEulerMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    ring

/-- Symplecticity does not imply exact energy preservation: at
`m = k = h = 1` the symplectic Euler step sends the state `(q, p) =
(0, 1)` to `(1, 1)`, whose oscillator energy `1` differs from the
initial energy `1 / 2`. -/
lemma symplecticEuler_energy_not_preserved :
    oscillatorEnergy 1 1
        ((symplecticEulerMatrix 1 1 1).mulVec ![0, 1]) ≠ oscillatorEnergy 1 1 ![0, 1] := by
  simp [oscillatorEnergy, symplecticEulerMatrix, Matrix.mulVec, Matrix.of_apply]

end MechanicalIntegrators
