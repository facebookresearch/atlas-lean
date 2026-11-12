/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Geophysical inversion: nullspace nonidentifiability

For a discrete ray-length matrix `A`, models `s` and `s + v` give the same
travel-time vector iff `A *ᵥ v = 0`.

## i. Overview

`A` is a finite real matrix of ray lengths, `s` a slowness model, `v` a
model perturbation, and the travel-time vector is `A *ᵥ s` (`Matrix.mulVec`).
Equal travel times for `s` and `s + v` are exactly the nullspace condition:
a perturbation in the nullspace of `A` is invisible to the data. A zero row
(a missing-ray cell) cannot see its slowness component, while a full-rank
(identity) matrix has trivial nullspace, so noiseless data recover the
model. Nullspace nonidentifiability; a regularized solution is not
necessarily the true Earth model.

## ii. Key results

- `EarthScience.travel_time_same_iff_nullspace`: same travel times iff
  `A *ᵥ v = 0`.
- `EarthScience.missing_ray_nullspace`: a missing-ray cell example.
- `EarthScience.identity_nullspace_trivial`: identity has trivial nullspace.

## iii. Table of contents

- A. Nullspace nonidentifiability

## iv. References

- `Matrix.mulVec_add`, `Matrix.one_mulVec` in Mathlib.

## A. Nullspace nonidentifiability
-/

@[expose] public section

open scoped Matrix

namespace EarthScience

set_option linter.unusedFintypeInType false in
/-- Nullspace nonidentifiability: models `s` and `s + v` give the same
travel-time vector iff `A *ᵥ v = 0`. -/
theorem travel_time_same_iff_nullspace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (s v : n → ℝ) :
    Matrix.mulVec A (s + v) = Matrix.mulVec A s ↔ Matrix.mulVec A v = 0 := by
  rw [Matrix.mulVec_add]
  constructor
  · intro h
    have h2 : Matrix.mulVec A s + Matrix.mulVec A v - Matrix.mulVec A s =
        Matrix.mulVec A s - Matrix.mulVec A s := by rw [h]
    simpa using h2
  · intro h
    rw [h, add_zero]

/-- Missing-ray cell: a ray-length matrix with a zero row cannot see the
corresponding slowness component. -/
theorem missing_ray_nullspace :
    Matrix.mulVec (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] = 0 ∧
      Matrix.mulVec (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] = ![1, 0] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]

/-- Noiseless full-rank recovery: the identity matrix has trivial nullspace. -/
theorem identity_nullspace_trivial (v : Fin 2 → ℝ)
    (hv : Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) v = 0) :
    v = 0 := by
  simpa [Matrix.one_mulVec] using hv

end EarthScience
