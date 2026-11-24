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
# Integral Pfaffians

The Pfaffian is defined by expansion along the first row, with the empty
Pfaffian equal to one. This is a polynomial with integer coefficients: no
division, characteristic assumption, or choice of a square root is involved.

The definition uses the strictly upper triangular entries of any matrix. On
alternating matrices (skew symmetric with zero diagonal, including in
characteristic two) it is the usual Pfaffian. In odd sizes the recursion gives
zero. Principal submatrices can be passed directly to `Matrix.pfaffian`.

The scalar-map theorem and the formulas in sizes zero, one, two and four are
the initial interface. Determinant identities, changes of basis, deletion
vectors and exterior divided powers are outside this leaf's scope.

Reference: D. A. Buchsbaum and D. Eisenbud, *Algebra Structures for Finite Free
Resolutions, and Some Structure Theorems for Ideals of Codimension 3* (1977),
§2, especially Lemma 2.4 and its Pfaffian expansion illustration.
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

universe u v

variable {R : Type u} [CommRing R]

/-- The integral Pfaffian, recursively expanded along the first row.
In each summand `j` indexes the partner of the first row in the remaining
`n + 1` indices; `j.succAbove` deletes that partner before `Fin.succ` restores
the original indexing. -/
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

/-- The first-row expansion, without any division. -/
theorem pfaffian_succ_succ {n : ℕ} (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    pfaffian A =
      ∑ j : Fin (n + 1), (-1 : R) ^ (j : ℕ) * A 0 j.succ *
        pfaffian (A.submatrix (fun i : Fin n => (j.succAbove i).succ)
          (fun i : Fin n => (j.succAbove i).succ)) := rfl

/-- The integral Pfaffian commutes with every homomorphism of commutative
rings, including reduction to positive characteristic. -/
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

/-- The three terms of the Pfaffian of a four by four matrix. -/
theorem pfaffian_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    pfaffian A = A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 := by
  simp [pfaffian, Fin.sum_univ_succ, Fin.succAbove, sub_eq_add_neg, add_assoc]

end Matrix
