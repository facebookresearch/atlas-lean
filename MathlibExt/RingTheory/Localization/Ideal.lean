/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Ideals as intersections of their localizations

An ideal of a commutative ring is the intersection of its localizations
at the maximal ideals, and also the intersection of its localizations
at the prime ideals. This is Corollary 2.7 of ATLAS `NumberTheoryI`,
Section 2.3. The book states it for an integral domain; the proof uses
only the colon-ideal argument, so it holds for any commutative ring.

## Main results

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

/-- An ideal equals the intersection of its localizations at the
maximal ideals: `I` is the infimum, over all `𝔪 : MaximalSpectrum A`,
of the contraction to `A` of `I` extended to `A_𝔪`. -/
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

/-- An ideal equals the intersection of its localizations at the
prime ideals: `I` is the infimum, over all `𝔭 : PrimeSpectrum A`, of
the contraction to `A` of `I` extended to `A_𝔭`. -/
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

/-- The intersections of the localizations at the maximal ideals and
at the prime ideals agree. -/
theorem iInf_comap_map_localization_maximal_eq_prime (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) =
    (⨅ 𝔭 : PrimeSpectrum A,
      (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) := by
  rw [eq_iInf_comap_map_localization_maximal,
    eq_iInf_comap_map_localization_prime]

end Ideal
