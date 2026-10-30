/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
Canonical ideal factorization, nonzero ideal classes and absolute index norm. No quadratic
conjugate-ideal norm formula or geometric lattice claim.
-/

set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors

example (K : Type*) [Field K] [NumberField K] :
    UniqueFactorizationMonoid (Ideal (NumberField.RingOfIntegers K)) := inferInstance

example (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (P : Ideal (NumberField.RingOfIntegers K))
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) : Prime P :=
  UniqueFactorizationMonoid.prime_of_normalized_factor P hP

example (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    Associated (UniqueFactorizationMonoid.normalizedFactors I).prod I :=
  UniqueFactorizationMonoid.prod_normalizedFactors hI

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J A : Ideal R) (hA : A ≠ ⊥) (h : I * A = J * A) : I = J :=
  mul_right_cancel₀ hA h

example {R : Type*} [CommRing R] [IsDedekindDomain R] (I J : Ideal R) :
    J ∣ I ↔ I ≤ J := Ideal.dvd_iff_le

example (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (NumberField.RingOfIntegers K)) := inferInstance

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J : (Ideal R)⁰) :
    ClassGroup.mk0 I = ClassGroup.mk0 J ↔
      ∃ (a b : R) (_ : a ≠ 0) (_ : b ≠ 0),
        Ideal.span {a} * (I : Ideal R) = Ideal.span {b} * (J : Ideal R) :=
  ClassGroup.mk0_eq_mk0_iff

example {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J A : (Ideal R)⁰) (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (I * A) = ClassGroup.mk0 (J * A) := by
  simp only [map_mul, h]

example (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.absNorm I = I.toAddSubgroup.index := Ideal.absNorm_eq_index I

example (K : Type*) [Field K] [NumberField K] :
    Ideal.absNorm (⊥ : Ideal (NumberField.RingOfIntegers K)) = 0 := map_zero Ideal.absNorm

example (R : Type*) [CommRing R] [IsDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI

#print axioms Ideal.uniqueFactorizationMonoid
#print axioms UniqueFactorizationMonoid.prime_of_normalized_factor
#print axioms UniqueFactorizationMonoid.prod_normalizedFactors
#print axioms Ideal.dvd_iff_le
#print axioms NumberField.RingOfIntegers.instFintypeClassGroup
#print axioms ClassGroup.mk0_eq_mk0_iff
#print axioms ClassGroup.mk0
#print axioms Ideal.absNorm
#print axioms Ideal.absNorm_eq_index
#print axioms Ideal.finiteQuotientOfFreeOfNeBot

end
