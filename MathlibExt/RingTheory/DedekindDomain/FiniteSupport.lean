/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Finite support of ideal valuations in a Dedekind domain

ATLAS `NumberTheoryI`, Section 3.2: Lemma 3.6, Corollary 3.7, Lemma 3.9 and
Corollary 3.10. Source: `v1/Atlas/NumberTheoryI/code/DedekindProperties.lean`,
ATLAS commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

In a Dedekind domain only finitely many prime ideals contain a given nonzero
element or ideal, the multiplicity of a prime in the factorization of an ideal
vanishes exactly when the prime does not contain the ideal, and the valuations
of a fractional ideal vanish at all but finitely many height-one primes.

## Source-to-API map

* `Ideal.finite_setOf_isPrime_and_mem` covers Lemma 3.6.
* `Ideal.finite_setOf_isPrime_and_le` covers Corollary 3.7.
* `Ideal.count_normalizedFactors_eq_zero_iff` covers Lemma 3.9.
* `FractionalIdeal.count_eq_zero_for_all_but_finitely_many` covers
  Corollary 3.10. It is stated without the book's nonzero hypothesis, since
  Mathlib's `FractionalIdeal.finite_factors` already handles the zero ideal
  (its valuations are all zero).

The proofs are short wrappers over Mathlib's `Ideal.finite_factors`,
`Ideal.mem_normalizedFactors_iff` and `FractionalIdeal.finite_factors`;
the packaged statements themselves are the new content.
-/

@[expose] public section

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

open scoped nonZeroDivisors

/-- Lemma 3.6: only finitely many prime ideals of a Dedekind domain contain a
given nonzero element. -/
theorem Ideal.finite_setOf_isPrime_and_mem {a : A} (ha : a ≠ 0) :
    Set.Finite {P : Ideal A | P.IsPrime ∧ a ∈ P} := by
  have hI : Ideal.span {a} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  refine Set.Finite.subset
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).toFinset.finite_toSet
    ?_
  intro P hP
  obtain ⟨hPPrime, haP⟩ := hP
  rw [Finset.mem_coe, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI]
  exact ⟨hPPrime, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr haP)⟩

/-- Corollary 3.7: only finitely many prime ideals of a Dedekind domain contain
a given nonzero ideal. -/
theorem Ideal.finite_setOf_isPrime_and_le {I : Ideal A} (hI : I ≠ ⊥) :
    {p : Ideal A | p.IsPrime ∧ I ≤ p}.Finite := by
  have hsub : {p : Ideal A | p.IsPrime ∧ I ≤ p} ⊆
      (fun v : IsDedekindDomain.HeightOneSpectrum A => v.asIdeal) ''
        {v : IsDedekindDomain.HeightOneSpectrum A | v.asIdeal ∣ I} := by
    intro p hp
    obtain ⟨hpPrime, hle⟩ := hp
    have hpne : p ≠ ⊥ := by
      intro h
      rw [h] at hle
      exact hI (eq_bot_iff.mpr hle)
    exact ⟨⟨p, hpPrime, hpne⟩, Ideal.dvd_iff_le.mpr hle, rfl⟩
  exact (Ideal.finite_factors hI).image _ |>.subset hsub

/-- Lemma 3.9: for a prime ideal `𝔭` and a nonzero ideal `I`, the multiplicity
of `𝔭` in the factorization of `I` is zero if and only if `𝔭` does not
contain `I`. In particular, the multiplicities of two distinct nonzero primes
in each other are zero. -/
theorem Ideal.count_normalizedFactors_eq_zero_iff
    {𝔭 I : Ideal A} (hp : 𝔭.IsPrime) (hI : I ≠ ⊥) :
    Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors I) = 0 ↔
      ¬(I ≤ 𝔭) := by
  rw [Multiset.count_eq_zero, Ideal.mem_normalizedFactors_iff hI]
  simp only [hp, true_and]

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- Corollary 3.10: for a fractional ideal `I` of a Dedekind domain, the
valuation `v ↦ FractionalIdeal.count K v I` is nonzero at only finitely many
height-one primes `v`. In particular, for `x ∈ Kˣ` the valuations
`v ↦ FractionalIdeal.count K v (spanSingleton x)` vanish for all but finitely
many `v`. -/
theorem FractionalIdeal.count_eq_zero_for_all_but_finitely_many
    (I : FractionalIdeal A⁰ K) :
    {v : IsDedekindDomain.HeightOneSpectrum A |
      FractionalIdeal.count K v I ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
