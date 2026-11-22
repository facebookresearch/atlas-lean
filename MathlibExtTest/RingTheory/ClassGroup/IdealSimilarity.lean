/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ClassGroup.IdealSimilarity

/-!
# Canonical nonzero ideal similarity tests

The source name unfolds to class-group equality. The fraction-field and balanced
witness descriptions, multiplication and principality use Mathlib directly.
Concrete integer ideals `(6)`, `(10)` and `(2)` exercise the source witnesses;
the nonzero carrier excludes the zero ideal structurally.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors
open IdealFactorization

namespace MathlibExtTest.RingTheory.ClassGroup.IdealSimilarity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The source name is definitionally the canonical class-group equality predicate. -/
theorem canonical_definition_test (I J : (Ideal R)⁰) :
    IdealsSimilar I J ↔ ClassGroup.mk0 I = ClassGroup.mk0 J := Iff.rfl

example (I : (Ideal R)⁰) : IdealsSimilar I I := rfl

example (I J : (Ideal R)⁰) (h : IdealsSimilar I J) : IdealsSimilar J I := h.symm

example (I J K : (Ideal R)⁰) (hIJ : IdealsSimilar I J) (hJK : IdealsSimilar J K) :
    IdealsSimilar I K := hIJ.trans hJK

example (I J A : (Ideal R)⁰) (h : IdealsSimilar I J) :
    IdealsSimilar (I * A) (J * A) := by
  simpa only [IdealsSimilar, map_mul] using congrArg (fun c => c * ClassGroup.mk0 A) h

example (I J : (Ideal R)⁰) :
    IdealsSimilar I J ↔ ∃ (a b : R) (_ : a ≠ 0) (_ : b ≠ 0),
      Ideal.span {a} * (I : Ideal R) = Ideal.span {b} * (J : Ideal R) :=
  ClassGroup.mk0_eq_mk0_iff

example (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (I J : (Ideal R)⁰) :
    IdealsSimilar I J ↔ ∃ (x : K) (_ : x ≠ 0),
      FractionalIdeal.spanSingleton R⁰ x *
        ((I : Ideal R) : FractionalIdeal R⁰ K) =
        ((J : Ideal R) : FractionalIdeal R⁰ K) :=
  ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K

example (I : (Ideal R)⁰) : IdealsSimilar I 1 ↔ (I : Ideal R).IsPrincipal := by
  simpa only [IdealsSimilar, map_one] using ClassGroup.mk0_eq_one_iff I.property

example (I : (Ideal R)⁰) : (I : Ideal R) ≠ 0 := nonZeroDivisors.ne_zero I.property

example : (⊥ : Ideal ℤ) ∉ (Ideal ℤ)⁰ := by simp [mem_nonZeroDivisors_iff_ne_zero]

private def nzPrincipal (n : ℤ) (hn : n ≠ 0) : (Ideal ℤ)⁰ :=
  ⟨Ideal.span {n}, mem_nonZeroDivisors_iff_ne_zero.mpr
    (mt (Ideal.span_singleton_eq_bot (x := n)).mp hn)⟩

private abbrev i6 : (Ideal ℤ)⁰ := nzPrincipal 6 (by norm_num)
private abbrev i10 : (Ideal ℤ)⁰ := nzPrincipal 10 (by norm_num)
private abbrev i2 : (Ideal ℤ)⁰ := nzPrincipal 2 (by norm_num)

private theorem six_ten_class_eq : ClassGroup.mk0 i6 = ClassGroup.mk0 i10 := by
  apply ClassGroup.mk0_eq_mk0_iff.mpr
  refine ⟨5, 3, by norm_num, by norm_num, ?_⟩
  change Ideal.span {(5 : ℤ)} * Ideal.span {(6 : ℤ)} =
    Ideal.span {(3 : ℤ)} * Ideal.span {(10 : ℤ)}
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  rfl

example : IdealsSimilar i6 i10 := six_ten_class_eq

example : IdealsSimilar (i6 * i2) (i10 * i2) := by
  simpa only [IdealsSimilar, map_mul] using
    congrArg (fun c => c * ClassGroup.mk0 i2) six_ten_class_eq

example : IdealsSimilar i6 1 := by
  change ClassGroup.mk0 i6 = ClassGroup.mk0 (1 : (Ideal ℤ)⁰)
  rw [map_one, ClassGroup.mk0_eq_one_iff i6.property]
  exact ⟨6, rfl⟩

#print axioms IdealFactorization.IdealsSimilar
#print axioms ClassGroup.mk0_eq_mk0_iff
#print axioms ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring
#print axioms ClassGroup.mk0_eq_one_iff
#print axioms six_ten_class_eq

end MathlibExtTest.RingTheory.ClassGroup.IdealSimilarity
