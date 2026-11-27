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

/-- **An ideal is the intersection of its contracted localizations at maximal ideals.** Let $A$
be a commutative ring and $I$ an ideal of $A$. For a maximal ideal $\mathfrak{m}$ of $A$, let
$\varphi_{\mathfrak{m}} \colon A \to A_{\mathfrak{m}}$ be the canonical map to the localization
of $A$ at $\mathfrak{m}$. Then
$I = \bigcap_{\mathfrak{m}} \varphi_{\mathfrak{m}}^{-1}(I A_{\mathfrak{m}})$, the intersection
over all maximal ideals $\mathfrak{m}$ of $A$: an ideal is the intersection of the contractions
to $A$ of its extensions to the localizations at the maximal ideals. -/
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

/-- **An ideal is the intersection of its contracted localizations at prime ideals.** Let $A$
be a commutative ring and $I$ an ideal of $A$. For a prime ideal $\mathfrak{p}$ of $A$, let
$\varphi_{\mathfrak{p}} \colon A \to A_{\mathfrak{p}}$ be the canonical map to the localization
of $A$ at $\mathfrak{p}$. Then
$I = \bigcap_{\mathfrak{p}} \varphi_{\mathfrak{p}}^{-1}(I A_{\mathfrak{p}})$, the intersection
over all prime ideals $\mathfrak{p}$ of $A$: an ideal is the intersection of the contractions
to $A$ of its extensions to the localizations at the prime ideals. -/
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

/-- **Contracted localizations of an ideal: the maximal and prime intersections agree.** Let $A$
be a commutative ring and $I$ an ideal of $A$. For a prime ideal $\mathfrak{p}$ of $A$, let
$\varphi_{\mathfrak{p}} \colon A \to A_{\mathfrak{p}}$ be the canonical map to the localization
of $A$ at $\mathfrak{p}$. Then
$\bigcap_{\mathfrak{m}} \varphi_{\mathfrak{m}}^{-1}(I A_{\mathfrak{m}}) =
\bigcap_{\mathfrak{p}} \varphi_{\mathfrak{p}}^{-1}(I A_{\mathfrak{p}})$, where the left
intersection runs over all maximal ideals $\mathfrak{m}$ of $A$ and the right one over all
prime ideals $\mathfrak{p}$ of $A$. -/
theorem iInf_comap_map_localization_maximal_eq_prime (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) =
    (⨅ 𝔭 : PrimeSpectrum A,
      (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) := by
  rw [eq_iInf_comap_map_localization_maximal,
    eq_iInf_comap_map_localization_prime]

/-- **The image of an ideal in the fraction field is the intersection of its localizations at
maximal ideals.** Let $A$ be an integral domain with fraction field $K$, let $I$ be an ideal of
$A$, and let $M \subseteq K$ be the image of $I$ under the canonical map $A \to K$, an
$A$-submodule of $K$. For a maximal ideal $\mathfrak{m}$ of $A$, let $M_{\mathfrak{m}}$ be the
localization of $M$ at $\mathfrak{m}$: the set of $x \in K$ such that $s x \in M$ for some
$s \in A \setminus \mathfrak{m}$. Then $M = \bigcap_{\mathfrak{m}} M_{\mathfrak{m}}$, the
intersection over all maximal ideals $\mathfrak{m}$ of $A$, taken inside $K$.

Source: ATLAS NumberTheoryI, Section 2.3, Corollary 2.7, maximal-ideal form. -/
theorem eq_iInf_localizedAt_maximal [IsDomain A] (K : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (Submodule.map (Algebra.linearMap A K) I).localizedAt
        𝔪.asIdeal.primeCompl) =
    Submodule.map (Algebra.linearMap A K) I :=
  Submodule.eq_iInf_localizedAt_maximal _

/-- **The image of an ideal in the fraction field is the intersection of its localizations at
prime ideals.** Let $A$ be an integral domain with fraction field $K$, let $I$ be an ideal of
$A$, and let $M \subseteq K$ be the image of $I$ under the canonical map $A \to K$, an
$A$-submodule of $K$. For a prime ideal $\mathfrak{p}$ of $A$, let $M_{\mathfrak{p}}$ be the
localization of $M$ at $\mathfrak{p}$: the set of $x \in K$ such that $s x \in M$ for some
$s \in A \setminus \mathfrak{p}$. Then $M = \bigcap_{\mathfrak{p}} M_{\mathfrak{p}}$, the
intersection over all prime ideals $\mathfrak{p}$ of $A$, taken inside $K$.

Source: ATLAS NumberTheoryI, Section 2.3, Corollary 2.7, prime-ideal form. -/
theorem eq_iInf_localizedAt_prime [IsDomain A] (K : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] (I : Ideal A) :
    (⨅ 𝔭 : PrimeSpectrum A,
      (Submodule.map (Algebra.linearMap A K) I).localizedAt
        𝔭.asIdeal.primeCompl) =
    Submodule.map (Algebra.linearMap A K) I :=
  Submodule.eq_iInf_localizedAt_prime _

end Ideal
