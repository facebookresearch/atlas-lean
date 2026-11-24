/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Unitary conjugation of matrices

This module defines conjugation of a square complex matrix by a unitary:

`U * A * Uᴴ` (i.e. `U * A * star U`), and establishes its basic laws: unfolding
to `U * A * star U`, preservation of positive semidefiniteness and trace,
identity and composition, and linearity with respect to addition, negation,
scalar multiplication, subtraction, and finite sums.

## Main definitions

* `Matrix.unitaryConj` – conjugation `U * A * star U`.

## Main results

* `unitaryConj_posSemidef` – PSD is preserved.
* `unitaryConj_trace` – trace is preserved.
* `unitaryConj_one` / `unitaryConj_mul` – identity and composition.
* `unitaryConj_zero`, `unitaryConj_add`, `unitaryConj_smul`, `unitaryConj_neg`,
  `unitaryConj_sub`, `unitaryConj_sum` – linearity and finite sums.
-/

@[expose] public section

open Matrix Finset
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary conjugation of a square matrix: `U * A * Uᴴ`. -/
def unitaryConj (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)

@[simp]
theorem unitaryConj_def (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    unitaryConj U A = (U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ) :=
  rfl

/-- Conjugation by a unitary preserves positive semidefiniteness,
via the pinned API `PosSemidef.mul_mul_conjTranspose_same`. -/
theorem unitaryConj_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (U : unitaryGroup n ℂ) : (unitaryConj U A).PosSemidef := by
  simp only [unitaryConj_def]
  exact hA.mul_mul_conjTranspose_same (U : Matrix n n ℂ)

/-- Conjugation by a unitary preserves trace, by cyclicity and
`star U * U = 1`. -/
theorem unitaryConj_trace (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    (unitaryConj U A).trace = A.trace := by
  have hUU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 :=
    UnitaryGroup.star_mul_self U
  calc
    (unitaryConj U A).trace = ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)).trace :=
      rfl
    _ = (A * star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)).trace := by
      rw [trace_mul_cycle _ _ _, trace_mul_cycle _ _ _]
    _ = (A * (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ))).trace := by
      rw [Matrix.mul_assoc]
    _ = (A * 1).trace := by rw [hUU]
    _ = A.trace := by simp

@[simp]
theorem unitaryConj_one (A : Matrix n n ℂ) : unitaryConj 1 A = A := by
  simp [unitaryConj]

theorem unitaryConj_mul (U V : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    unitaryConj (U * V) A = unitaryConj U (unitaryConj V A) := by
  simp only [unitaryConj_def, UnitaryGroup.mul_val, star_mul, Matrix.mul_assoc]

/-- Unitary conjugation sends `0` to `0`. -/
@[simp]
theorem unitaryConj_zero (U : unitaryGroup n ℂ) :
    unitaryConj U (0 : Matrix n n ℂ) = 0 := by
  simp [unitaryConj]

/-- Unitary conjugation distributes over addition. -/
@[simp]
theorem unitaryConj_add (U : unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    unitaryConj U (A + B) = unitaryConj U A + unitaryConj U B := by
  simp [unitaryConj_def, mul_add, add_mul]

/-- Unitary conjugation commutes with scalar action. -/
@[simp]
theorem unitaryConj_smul {R : Type*} [Monoid R] [DistribMulAction R ℂ]
    [SMulCommClass R ℂ ℂ] [IsScalarTower R ℂ ℂ]
    (U : unitaryGroup n ℂ) (c : R) (A : Matrix n n ℂ) :
    unitaryConj U (c • A) = c • unitaryConj U A := by
  simp only [unitaryConj_def]
  calc (U : Matrix n n ℂ) * (c • A) * star (U : Matrix n n ℂ)
      = ((U : Matrix n n ℂ) * (c • A)) * star (U : Matrix n n ℂ) := by rw [Matrix.mul_assoc]
    _ = (c • ((U : Matrix n n ℂ) * A)) * star (U : Matrix n n ℂ) := by rw [Matrix.mul_smul]
    _ = c • (((U : Matrix n n ℂ) * A) * star (U : Matrix n n ℂ)) := by rw [smul_mul]
    _ = _ := by rw [Matrix.mul_assoc]

/-- Unitary conjugation sends negation to negation. -/
@[simp]
theorem unitaryConj_neg (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    unitaryConj U (-A) = - unitaryConj U A := by
  simp [unitaryConj_def, neg_mul, mul_neg]

/-- Unitary conjugation distributes over subtraction. -/
@[simp]
theorem unitaryConj_sub (U : unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    unitaryConj U (A - B) = unitaryConj U A - unitaryConj U B := by
  simp [unitaryConj_def, mul_sub, sub_mul]

variable {ι : Type*}

/-- Unitary conjugation distributes over finite sums. -/
theorem unitaryConj_sum (U : unitaryGroup n ℂ) (s : Finset ι)
    (f : ι → Matrix n n ℂ) :
    unitaryConj U (∑ i ∈ s, f i) = ∑ i ∈ s, unitaryConj U (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, unitaryConj_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, unitaryConj_add, ih]

end Matrix
