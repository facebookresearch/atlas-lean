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
# Idempotent matrix lifting across a nilpotent quotient

Ordered coefficient products place each matrix-power entry in the
corresponding ideal power. A nilpotent ideal consequently makes the
actual entrywise quotient matrix kernel elementwise nilpotent. The
existing general-ring idempotent-lifting theorem then supplies an
idempotent matrix with the caller's exact original quotient image.

Source: Weibel, *The K-book*, I.Exercise 2.2, the matrix step of
projective nilpotent reduction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped BigOperators

universe u v

namespace Matrix

section Semiring

variable {R : Type u} [Semiring R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The entries of an actual matrix power lie in the same ordered ideal power. -/
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

/-- Every actual matrix killed by the nilpotent quotient map is nilpotent. -/
theorem isNilpotent_of_quotient_map_eq_zero (hI : IsNilpotent I) (A : Matrix n n R)
    (hA : (Ideal.Quotient.mk I).mapMatrix A = 0) : IsNilpotent A := by
  apply isNilpotent_of_entries_mem_ideal I hI A
  intro i j
  have h := congrArg (fun B : Matrix n n (R ⧸ I) => B i j) hA
  change Ideal.Quotient.mk I (A i j) = 0 at h
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

/-- A target idempotent matrix lifts to an actual idempotent source matrix
whose original entrywise quotient map has precisely the specified value. -/
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
