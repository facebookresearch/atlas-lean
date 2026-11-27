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
# Pivot elimination and determinant identities

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). For P = [[a,r],[c,B]], the elimination matrix E = [[1,0],[−c,aI]] gives E P =
[[a,r],[0,S]] with S = aB − cr. The identities det E = a^|I| and a det S = a^|I| det P hold
for every a, including zero, and for the empty lower block.
-/

@[expose] public section
noncomputable section

universe u v

namespace Matrix

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **A matrix with a distinguished pivot.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). The matrix P on 1 ⊕ I is P = [[a,r],[c,B]], where its singleton diagonal block
is multiplication by a.
-/
def pivotBlock (a : R) (r : Matrix Unit ι R) (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  Matrix.fromBlocks (a • (1 : Matrix Unit Unit R)) r c B

/-- **The pivot elimination matrix.**

For a commutative ring R, finite I, a ∈ R and c ∈ Mat(I,1;R), define E = [[1,0],[−c,aI]] on 1
⊕ I. This formula uses multiplication and subtraction and is defined for every pivot a.
-/
def pivotElimination (a : R) (c : Matrix ι Unit R) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 (-c) (a • (1 : Matrix ι ι R))

/-- **The Schur numerator.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). Define S = aB − cr, a square matrix on I. Its entries are Sᵢⱼ = a Bᵢⱼ − cᵢ rⱼ.
-/
def pivotSchur (a : R) (r : Matrix Unit ι R) (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    Matrix ι ι R := a • B - c * r

/-- **Upper block form after pivot elimination.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). For P = [[a,r],[c,B]], E = [[1,0],[−c,aI]], and S = aB − cr, one has E P =
[[a,r],[0,S]]. The equality holds for arbitrary a.
-/
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

/-- **Determinant of the elimination matrix.**

For a commutative ring R, finite I, a ∈ R and c ∈ Mat(I,1;R), the matrix E = [[1,0],[−c,aI]]
satisfies det E = a^|I|. In particular, the empty lower block gives det E = 1.
-/
theorem det_pivotElimination (a : R) (c : Matrix ι Unit R) :
    (pivotElimination a c).det = a ^ Fintype.card ι := by
  unfold pivotElimination
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
    Matrix.det_smul, Matrix.det_one, mul_one]

/-- **The pivot and Schur determinant relation.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). For P = [[a,r],[c,B]] and S = aB − cr, the identity a det S = a^|I| det P
holds over R, including zero or noninvertible pivots.
-/
theorem det_pivotSchur_relation (a : R) (r : Matrix Unit ι R)
    (c : Matrix ι Unit R) (B : Matrix ι ι R) :
    a * (pivotSchur a r c B).det =
      a ^ Fintype.card ι * (pivotBlock a r c B).det := by
  have h := Matrix.det_mul (pivotElimination a c) (pivotBlock a r c B)
  rw [pivotElimination_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one,
    Fintype.card_unit, pow_one, mul_one, det_pivotElimination] at h
  exact h

/-- **A nonzero Schur determinant.**

Let R be a commutative ring, I a finite index type, a ∈ R, r ∈ Mat(1,I;R), c ∈ Mat(I,1;R), and
B ∈ Mat(I,I;R). Assume R is a domain, a ≠ 0, and det [[a,r],[c,B]] ≠ 0. Then det(aB − cr) ≠ 0.
-/
theorem det_pivotSchur_ne_zero [IsDomain R] (a : R) (ha : a ≠ 0)
    (r : Matrix Unit ι R) (c : Matrix ι Unit R) (B : Matrix ι ι R)
    (hA : (pivotBlock a r c B).det ≠ 0) : (pivotSchur a r c B).det ≠ 0 := by
  intro hS
  have h := det_pivotSchur_relation a r c B
  rw [hS, mul_zero] at h
  exact (mul_ne_zero (pow_ne_zero _ ha) hA) h.symm

end Matrix
