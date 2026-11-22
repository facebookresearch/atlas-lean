/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LaurentPolynomial_uniqueFactorizationMonoid.lean`
and
`P2M/Sol/S_LaurentPolynomial_uniqueFactorizationMonoid.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

open LaurentPolynomial
open scoped Polynomial

private theorem uniqueFactorizationMonoid_of_isLocalization
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    UniqueFactorizationMonoid S := by
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun J hJ hJp => ?_
  haveI := hJp
  set I : Ideal R := J.under R with hI
  haveI hIp : I.IsPrime := Ideal.IsPrime.under R J
  have hI0 : I ≠ ⊥ := by
    intro h0
    apply hJ
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M s
    have hr : algebraMap R S r ∈ J := by
      have := J.mul_mem_left (algebraMap R S m) hs
      rwa [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left] at this
    have hrI : r ∈ I := Ideal.mem_comap.mpr hr
    rw [h0, Ideal.mem_bot] at hrI
    rw [Submodule.mem_bot, hrI]
    exact IsLocalization.mk'_zero _
  obtain ⟨p, hpI, hp⟩ :=
    (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp ‹_› I hI0 hIp)
  refine ⟨algebraMap R S p, Ideal.mem_comap.mp hpI, ?_⟩
  have hdisj : Disjoint (M : Set R) (Ideal.span {p} : Set R) := by
    rw [Set.disjoint_left]
    intro m hm hmp
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hmp
    have hu : IsUnit (algebraMap R S (c * p)) := IsLocalization.map_units S ⟨c * p, hm⟩
    rw [map_mul] at hu
    exact hJp.ne_top (J.eq_top_of_isUnit_mem (Ideal.mem_comap.mp hpI)
      (isUnit_of_mul_isUnit_right hu))
  have hprime : (Ideal.map (algebraMap R S) (Ideal.span {p})).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S _
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hdisj
  rw [Ideal.map_span, Set.image_singleton] at hprime
  have hp0 : algebraMap R S p ≠ 0 := fun h =>
    hp.ne_zero ((IsLocalization.injective S hM) (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hp0).mp hprime

namespace LaurentPolynomial

/-- Laurent polynomials over a unique factorization domain form a unique
factorization domain.

Laurent polynomials are the localization of polynomials at the powers of
`X`, and a localization of a unique factorization domain at a submonoid of
non-zero-divisors is again a unique factorization domain by Kaplansky's
criterion. -/
public theorem uniqueFactorizationMonoid
    (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] :=
  uniqueFactorizationMonoid_of_isLocalization (Submonoid.powers (Polynomial.X : R[X]))
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero) R[T;T⁻¹]

end LaurentPolynomial
