/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Integral Pfaffian by first-row expansion

Let R be a commutative ring and A a square matrix indexed by Fin n. The integral Pfaffian has
pf_0=1, pf_1=0 and pf_(n+2)(A)=∑_{j=1}^{n+1}(-1)^(j-1) A_(0,j) pf(A with rows and columns 0,j
deleted in order). This is an integer-coefficient polynomial using the strictly upper
triangular entries. It gives the usual Pfaffian for alternating matrices, applies in every
characteristic and is zero in odd sizes. In size 4 it is A01*A23-A02*A13+A03*A12.

Reference: D. A. Buchsbaum and D. Eisenbud, Algebra Structures for Finite Free Resolutions,
and Some Structure Theorems for Ideals of Codimension 3 (1977), §2, especially Lemma 2.4 and
its Pfaffian expansion illustration.
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

universe u v

variable {R : Type u} [CommRing R]

/-- **First-row recursive integral Pfaffian.**

Let R be a commutative ring and A a square matrix indexed by Fin n. The integral Pfaffian has
pf_0=1, pf_1=0 and pf_(n+2)(A)=∑_{j=1}^{n+1}(-1)^(j-1) A_(0,j) pf(A with rows and columns 0,j
deleted in order). This defines pfaffian for every square matrix, with no alternating-matrix
premise on the input.
-/
def pfaffian : {n : ℕ} → Matrix (Fin n) (Fin n) R → R
  | 0, _ => 1
  | 1, _ => 0
  | n + 2, A =>
      ∑ j : Fin (n + 1), (-1 : R) ^ (j : ℕ) * A 0 j.succ *
        pfaffian (A.submatrix (fun i : Fin n => (j.succAbove i).succ)
          (fun i : Fin n => (j.succAbove i).succ))

@[simp]
theorem pfaffian_fin_zero (A : Matrix (Fin 0) (Fin 0) R) :
    pfaffian A = 1 := rfl

@[simp]
theorem pfaffian_fin_one (A : Matrix (Fin 1) (Fin 1) R) :
    pfaffian A = 0 := rfl

/-- **Pfaffian expansion along the first row.**

Let R be a commutative ring and A a square matrix indexed by Fin n. The integral Pfaffian has
pf_0=1, pf_1=0 and pf_(n+2)(A)=∑_{j=1}^{n+1}(-1)^(j-1) A_(0,j) pf(A with rows and columns 0,j
deleted in order). For an (n+2)×(n+2) matrix, the displayed sum ranges over the partners
j=1,…,n+1 of the first index, with the induced ordered principal minor.
-/
theorem pfaffian_succ_succ {n : ℕ} (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    pfaffian A =
      ∑ j : Fin (n + 1), (-1 : R) ^ (j : ℕ) * A 0 j.succ *
        pfaffian (A.submatrix (fun i : Fin n => (j.succAbove i).succ)
          (fun i : Fin n => (j.succAbove i).succ)) := rfl

/-- **Pfaffian commutes with coefficient homomorphisms.**

Let R,S be commutative rings, f:R→S a ring homomorphism and A an n×n matrix over R. Then
pfaffian(A.map f)=f(pfaffian A), in all characteristics.
-/
theorem pfaffian_map {S : Type v} [CommRing S] (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    pfaffian (A.map f) = f (pfaffian A) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih _ =>
      simp only [pfaffian_succ_succ, map_sum, map_mul, map_pow, map_neg, map_one]
      apply Finset.sum_congr rfl
      intro j _
      rw [← ih (A.submatrix (fun i : Fin n => (j.succAbove i).succ)
        (fun i : Fin n => (j.succAbove i).succ))]
      rfl

@[simp]
theorem pfaffian_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    pfaffian A = A 0 1 := by
  simp [pfaffian]

/-- **Four-by-four Pfaffian formula.**

Let R be a commutative ring and A a 4×4 matrix over R. Then pfaffian
A=A01*A23-A02*A13+A03*A12.
-/
theorem pfaffian_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    pfaffian A = A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 := by
  simp [pfaffian, Fin.sum_univ_succ, Fin.succAbove, sub_eq_add_neg, add_assoc]

end Matrix
