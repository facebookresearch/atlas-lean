/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Idempotent matrix lifting through a nilpotent ideal

Let R be a ring, I a nilpotent two-sided ideal and n a finite matrix index. Every idempotent B
over R/I lifts to an idempotent A over R with q_*(A)=B. A matrix killed by q_* is nilpotent.
The entry estimate places A^k in the kth ideal power when all entries of A lie in I.

Source: Weibel, The K-book, I.Exercise 2.2, the matrix step of projective nilpotent reduction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped BigOperators

universe u v

namespace Matrix

section Semiring

variable {R : Type u} [Semiring R] {n : Type v} [Fintype n] [DecidableEq n]

/-- **Entries of a matrix power lie in the corresponding ideal power.**

Let R be a semiring, I an ideal, n a finite index type and A:Matrix n n R have every entry in
I. For k∈ℕ and i,j∈n, (A^k)_(i,j) belongs to I^k.
-/
theorem pow_apply_mem_ideal_pow (I : Ideal R) (A : Matrix n n R)
    (hA : ∀ i j, A i j ∈ I) (k : ℕ) (i j : n) : (A ^ k) i j ∈ I ^ k := by
  induction k generalizing i j with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply, Submodule.pow_succ]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.mul_mem_mul (ih i l) (hA l j)

private theorem isNilpotent_of_entries_mem_ideal (I : Ideal R) (hI : IsNilpotent I)
    (A : Matrix n n R) (hA : ∀ i j, A i j ∈ I) : IsNilpotent A := by
  obtain ⟨k, hk⟩ := hI
  refine ⟨k, Matrix.ext fun i j => ?_⟩
  change (A ^ k) i j = 0
  have h := pow_apply_mem_ideal_pow I A hA k i j
  rw [hk] at h
  simpa only [Ideal.zero_eq_bot, Submodule.mem_bot] using h

end Semiring

section Ring

variable {R : Type u} [Ring R] {n : Type v} [Fintype n] [DecidableEq n]
variable (I : Ideal R) [I.IsTwoSided]

/-- **Matrix kernel of a nilpotent quotient consists of nilpotents.**

Let R be a ring, I a nilpotent two-sided ideal, n finite and A:Matrix n n R. If entrywise
quotient reduction q_*(A)=0 in Matrix n n(R/I), then A is nilpotent.
-/
theorem isNilpotent_of_quotient_map_eq_zero (hI : IsNilpotent I) (A : Matrix n n R)
    (hA : (Ideal.Quotient.mk I).mapMatrix A = 0) : IsNilpotent A := by
  apply isNilpotent_of_entries_mem_ideal I hI A
  intro i j
  have h := congrArg (fun B : Matrix n n (R ⧸ I) => B i j) hA
  change Ideal.Quotient.mk I (A i j) = 0 at h
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

/-- **Lifting an idempotent matrix across a nilpotent quotient.**

Let R be a ring, I a nilpotent two-sided ideal and n finite. For B∈Matrix n n(R/I) with B²=B,
there exists A∈Matrix n n R with A²=A and entrywise quotient image q_*(A)=B.
-/
theorem exists_isIdempotentElem_quotient_lift
    (hI : IsNilpotent I) (B : Matrix n n (R ⧸ I)) (hB : IsIdempotentElem B) :
    ∃ A : Matrix n n R, IsIdempotentElem A ∧ (Ideal.Quotient.mk I).mapMatrix A = B := by
  classical
  let f : Matrix n n R →+* Matrix n n (R ⧸ I) := (Ideal.Quotient.mk I).mapMatrix
  have hker : ∀ A ∈ RingHom.ker f, IsNilpotent A := by
    intro A hA
    exact isNilpotent_of_quotient_map_eq_zero I hI A (RingHom.mem_ker.mp hA)
  have hsurj : Function.Surjective f := by
    have hq : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
    intro C
    let A : Matrix n n R := fun i j => Function.surjInv hq (C i j)
    refine ⟨A, Matrix.ext fun i j => ?_⟩
    exact Function.surjInv_eq hq (C i j)
  exact _root_.exists_isIdempotentElem_eq_of_ker_isNilpotent f hker B (hsurj B) hB

end Ring

end Matrix
