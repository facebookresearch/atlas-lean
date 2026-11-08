/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Localization.Submodule

/-!
# Ideals as intersections of their localizations

For an integral domain `A` with fraction field `K`, the image of an ideal
of `A` in `K` is the intersection of its localizations at the maximal
ideals, and also at the prime ideals. The intersections are submodules
of the common field `K`, including when the ideal is `⊤`. This is
Corollary 2.7 of ATLAS `NumberTheoryI`, Section 2.3, with the ambient
space fixed by Proposition 2.6.

The contraction criteria below hold for any commutative ring. They
intersect the extensions after contracting back to `A`.

## Main results

* `Ideal.eq_iInf_localizedAt_maximal` /
  `Ideal.eq_iInf_localizedAt_prime`: the ideal image in its fraction
  field equals the intersection of its localized images.
* `Ideal.eq_iInf_comap_map_localization_maximal`: an ideal equals the
  intersection, over all maximal ideals, of the contractions of its
  extensions to the corresponding localizations.
* `Ideal.eq_iInf_comap_map_localization_prime`: the same with prime
  ideals in place of maximal ideals.
* `Ideal.iInf_comap_map_localization_maximal_eq_prime`: the two
  intersections agree.
-/

@[expose] public section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- An ideal equals the intersection of the contractions of its
extensions at the maximal ideals. -/
theorem eq_iInf_comap_map_localization_maximal (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) = I := by
  ext x
  simp only [Ideal.mem_iInf]
  constructor
  · intro hx
    by_contra hxI
    have hJ : I.colon (Ideal.span {x}) ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one, Ideal.mem_colon_span_singleton]
      simpa using hxI
    obtain ⟨𝔪, h𝔪max, hJ𝔪⟩ :=
      (I.colon (Ideal.span {x})).exists_le_maximal hJ
    specialize hx ⟨𝔪, h𝔪max⟩
    rw [Ideal.mem_comap,
      IsLocalization.algebraMap_mem_map_algebraMap_iff
        𝔪.primeCompl] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    exact hs (hJ𝔪 (Ideal.mem_colon_span_singleton.mpr hsx))
  · intro hxI 𝔪
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hxI

/-- An ideal equals the intersection of the contractions of its
extensions at the prime ideals. -/
theorem eq_iInf_comap_map_localization_prime (I : Ideal A) :
    (⨅ 𝔭 : PrimeSpectrum A,
      (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) = I := by
  ext x
  simp only [Ideal.mem_iInf]
  constructor
  · intro hx
    rw [← eq_iInf_comap_map_localization_maximal I]
    simp only [Ideal.mem_iInf]
    exact fun 𝔪 => hx ⟨𝔪.asIdeal, 𝔪.isMaximal.isPrime⟩
  · intro hxI 𝔭
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hxI

/-- The intersections of localization contractions at the maximal
ideals and at the prime ideals agree. -/
theorem iInf_comap_map_localization_maximal_eq_prime (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) =
    (⨅ 𝔭 : PrimeSpectrum A,
      (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) := by
  rw [eq_iInf_comap_map_localization_maximal,
    eq_iInf_comap_map_localization_prime]

/-- Corollary 2.7, maximal-ideal form: the image of `I` in the fraction
field `K` equals the intersection of its localizations inside `K`.
Membership in a localized image means that some denominator outside
the maximal ideal scales the element into the image of `I`. -/
theorem eq_iInf_localizedAt_maximal [IsDomain A] (K : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (Submodule.map (Algebra.linearMap A K) I).localizedAt
        𝔪.asIdeal.primeCompl) =
    Submodule.map (Algebra.linearMap A K) I :=
  Submodule.eq_iInf_localizedAt_maximal _

/-- Corollary 2.7, prime-ideal form: the image of `I` in the fraction
field `K` equals the intersection of its localizations inside `K`. -/
theorem eq_iInf_localizedAt_prime [IsDomain A] (K : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] (I : Ideal A) :
    (⨅ 𝔭 : PrimeSpectrum A,
      (Submodule.map (Algebra.linearMap A K) I).localizedAt
        𝔭.asIdeal.primeCompl) =
    Submodule.map (Algebra.linearMap A K) I :=
  Submodule.eq_iInf_localizedAt_prime _

end Ideal
