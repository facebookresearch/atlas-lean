/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Division-free pivot elimination for arbitrary matrix size

The literal elimination matrix multiplies the original block matrix. Its
determinant relation uses no invertible-pivot or normality premise, and the
empty lower block is included. This is the matrix identity needed by the
singular determinant/cokernel-length induction.
-/

@[expose] public section
noncomputable section

universe u v

namespace Matrix

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The original pivot matrix, including both full off-diagonal blocks. -/
def pivotBlock (a : R) (r : Matrix Unit ι R) (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  Matrix.fromBlocks (a • (1 : Matrix Unit Unit R)) r c B

/-- The actual lower elimination matrix, with no division by its pivot. -/
def pivotElimination (a : R) (c : Matrix ι Unit R) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 (-c) (a • (1 : Matrix ι ι R))

/-- The full Schur matrix produced by the literal elimination. -/
def pivotSchur (a : R) (r : Matrix Unit ι R) (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    Matrix ι ι R := a • B - c * r

/-- Multiplication by the actual elimination matrix earns the full upper
block form, without a unit-pivot or nonzero-pivot hypothesis. -/
theorem pivotElimination_mul (a : R) (r : Matrix Unit ι R)
    (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    pivotElimination a c * pivotBlock a r c B =
      Matrix.fromBlocks (a • (1 : Matrix Unit Unit R)) r 0 (pivotSchur a r c B) := by
  have hc : c * (a • (1 : Matrix Unit Unit R)) = a • c := by
    ext i j
    cases j
    simp [Matrix.mul_apply, mul_comm]
  unfold pivotElimination pivotBlock pivotSchur
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.one_mul, hc, neg_add_cancel]
  have hd : -(c * r) + a • B = a • B - c * r := by
    simpa only [sub_eq_add_neg] using (add_comm (-(c * r)) (a • B))
  exact congrArg (fun D : Matrix ι ι R =>
    Matrix.fromBlocks (a • (1 : Matrix Unit Unit R)) r (0 : Matrix ι Unit R) D) hd

/-- The original elimination determinant is the exact pivot power for
every lower-block size, including the empty lower block. -/
theorem det_pivotElimination (a : R) (c : Matrix ι Unit R) :
    (pivotElimination a c).det = a ^ Fintype.card ι := by
  unfold pivotElimination
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
    Matrix.det_smul, Matrix.det_one, mul_one]

/-- The division-free determinant identity of the actual full pivot and
Schur matrices, valid over singular rings and for every matrix size. -/
theorem det_pivotSchur_relation (a : R) (r : Matrix Unit ι R)
    (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    a * (pivotSchur a r c B).det =
      a ^ Fintype.card ι * (pivotBlock a r c B).det := by
  have h := Matrix.det_mul (pivotElimination a c) (pivotBlock a r c B)
  rw [pivotElimination_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one,
    Fintype.card_unit, pow_one, mul_one, det_pivotElimination] at h
  exact h

/-- The actual Schur determinant remains nonzero for a nonzero original
determinant and pivot, through the division-free identity. -/
theorem det_pivotSchur_ne_zero [IsDomain R] (a : R) (ha : a ≠ 0)
    (r : Matrix Unit ι R) (c : Matrix ι Unit R) (B : Matrix ι ι R)
    (hA : (pivotBlock a r c B).det ≠ 0) : (pivotSchur a r c B).det ≠ 0 := by
  intro hS
  have h := det_pivotSchur_relation a r c B
  rw [hS, mul_zero] at h
  exact (mul_ne_zero (pow_ne_zero _ ha) hA) h.symm

end Matrix
