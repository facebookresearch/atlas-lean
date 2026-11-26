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
# Unitary conjugation of finite complex matrices

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. This map is complex-linear, preserves trace and positive
semidefiniteness, sends I-conjugation to the identity, and composes by C_(UV)=C_U∘C_V.
-/

@[expose] public section

open Matrix Finset
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Conjugation by a unitary matrix.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. This is the matrix unitaryConj U A.
-/
def unitaryConj (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)

@[simp]
theorem unitaryConj_def (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    unitaryConj U A = (U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ) :=
  rfl

/-- **Unitary conjugation preserves positive semidefiniteness.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. If A is positive semidefinite, then UAUᴴ is positive
semidefinite.
-/
theorem unitaryConj_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (U : unitaryGroup n ℂ) : (unitaryConj U A).PosSemidef := by
  simp only [unitaryConj_def]
  exact hA.mul_mul_conjTranspose_same (U : Matrix n n ℂ)

/-- **Trace is invariant under unitary conjugation.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. The trace identity is tr(unitaryConj U A)=tr(A).
-/
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

/-- **Unitary conjugation of the zero matrix.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. For A=0, C_U(0)=0.
-/
@[simp]
theorem unitaryConj_zero (U : unitaryGroup n ℂ) :
    unitaryConj U (0 : Matrix n n ℂ) = 0 := by
  simp [unitaryConj]

/-- **Additivity of unitary conjugation.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. For square matrices A,B, C_U(A+B)=C_U(A)+C_U(B).
-/
@[simp]
theorem unitaryConj_add (U : unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    unitaryConj U (A + B) = unitaryConj U A + unitaryConj U B := by
  simp [unitaryConj_def, mul_add, add_mul]

/-- **Scalar actions commute with unitary conjugation.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. Let R be a monoid acting distributively on ℂ, compatibly with
multiplication on both sides: c•(zw)=(c•z)w=z(c•w). For c∈R, C_U(c•A)=c•C_U(A).
-/
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

/-- **Unitary conjugation respects negation.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. The equality C_U(-A)=-C_U(A) holds.
-/
@[simp]
theorem unitaryConj_neg (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    unitaryConj U (-A) = - unitaryConj U A := by
  simp [unitaryConj_def, neg_mul, mul_neg]

/-- **Unitary conjugation respects subtraction.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. For square matrices A,B, C_U(A-B)=C_U(A)-C_U(B).
-/
@[simp]
theorem unitaryConj_sub (U : unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    unitaryConj U (A - B) = unitaryConj U A - unitaryConj U B := by
  simp [unitaryConj_def, mul_sub, sub_mul]

variable {ι : Type*}

/-- **Unitary conjugation of a finite matrix sum.**

Let I be a finite index type, U∈U(I,ℂ) a unitary matrix and A an I×I complex matrix. Write
C_U(A)=unitaryConj U A=U*A*Uᴴ. For a finite set s⊂J and square matrices A_j, C_U(∑j∈s
A_j)=∑j∈s C_U(A_j).
-/
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
