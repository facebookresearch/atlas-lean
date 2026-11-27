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
# Submodules as intersections of their localizations

A submodule of an `A`-module is the intersection of its localizations
at the maximal ideals, and also the intersection of its localizations
at the prime ideals. This is Proposition 2.6 of ATLAS `NumberTheoryI`,
Section 2.3. The book states it for a submodule of a vector space over
the fraction field of a domain; the proof uses only the colon-ideal
argument, so it holds for a submodule of an arbitrary module over an
arbitrary commutative ring, with no domain, field, or finiteness
hypothesis.

## Main results

* `Submodule.localizedAt`: the saturation of a submodule at a submonoid:
  the elements that land in the submodule after scaling by some element
  of the submonoid.
* `Submodule.mem_of_forall_mem_localizedAt_maximal`: an element lying in
  the localization at every maximal ideal lies in the submodule.
* `Submodule.mem_of_forall_mem_localizedAt_prime`: the same with prime
  ideals in place of maximal ideals.
* `Submodule.eq_iInf_localizedAt_maximal` /
  `Submodule.eq_iInf_localizedAt_prime`: a submodule equals the
  intersection of its localizations at the maximal / prime ideals.
* `Submodule.eq_iInf_localizedAt_maximal_eq_prime`: the two
  intersections agree.
-/

@[expose] public section

namespace Submodule

variable {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]

/-- **Saturation of a submodule at a submonoid.** Let $A$ be a commutative ring, $V$ an
$A$-module, $M$ a submodule of $V$ and $S$ a submonoid of $A$. The saturation of $M$ at $S$ is the
submodule of $V$ consisting of the elements $v \in V$ such that $s v \in M$ for some $s \in S$.

Writing $S^{-1}V$ for the localization of $V$ at $S$ and $S^{-1}M \subseteq S^{-1}V$ for that of
$M$, it is the preimage of $S^{-1}M$ under the localization map $V \to S^{-1}V$, that is, the
contraction to $V$ of the extension of $M$ to the localization at $S$. -/
def localizedAt (M : Submodule A V) (S : Submonoid A) : Submodule A V where
  carrier := {v | ∃ s ∈ S, s • v ∈ M}
  add_mem' := by
    rintro a b ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, ?_⟩
    have h : (s₁ * s₂) • (a + b) = s₂ • (s₁ • a) + s₁ • (s₂ • b) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm s₁ s₂ a, smul_comm s₁ s₂ b]
    rw [h]
    exact M.add_mem (M.smul_mem _ h₁) (M.smul_mem _ h₂)
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  smul_mem' := by
    rintro c v ⟨s, hs, h⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ h⟩

/-- **Membership in the saturation.** Let $A$ be a commutative ring, $V$ an $A$-module, $M$ a
submodule of $V$ and $S$ a submonoid of $A$. An element $v \in V$ lies in the saturation of $M$ at
$S$ if and only if $s v \in M$ for some $s \in S$. -/
theorem mem_localizedAt {M : Submodule A V} {S : Submonoid A} {v : V} :
    v ∈ M.localizedAt S ↔ ∃ s ∈ S, s • v ∈ M :=
  Iff.rfl

/-- **Membership is detected at the maximal ideals.** Let $A$ be a commutative ring, $V$ an
$A$-module, $M$ a submodule of $V$ and $v \in V$. Suppose that for every maximal ideal
$\mathfrak m$ of $A$, $v$ lies in the saturation of $M$ at $A \setminus \mathfrak m$, that is,
$s v \in M$ for some $s \in A \setminus \mathfrak m$. Then $v \in M$.

Source: ATLAS NumberTheoryI, Section 2.3, Proposition 2.6, element form. -/
theorem mem_of_forall_mem_localizedAt_maximal (M : Submodule A V) {v : V}
    (h : ∀ 𝔪 : MaximalSpectrum A, v ∈ M.localizedAt 𝔪.asIdeal.primeCompl) :
    v ∈ M := by
  classical
  let I : Ideal A := M.comap (LinearMap.toSpanSingleton A V v)
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm_max, hIm⟩ := I.exists_le_maximal hI
    obtain ⟨s, hs, hsv⟩ := h ⟨m, hm_max⟩
    have hsI : s ∈ I := by
      rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      exact hsv
    exact hs (hIm hsI)
  have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] at h1
  exact h1

/-- **Membership is detected at the prime ideals.** Let $A$ be a commutative ring, $V$ an
$A$-module, $M$ a submodule of $V$ and $v \in V$. Suppose that for every prime ideal
$\mathfrak p$ of $A$, $v$ lies in the saturation of $M$ at $A \setminus \mathfrak p$, that is,
$s v \in M$ for some $s \in A \setminus \mathfrak p$. Then $v \in M$.

Source: ATLAS NumberTheoryI, Section 2.3, Proposition 2.6, element form. -/
theorem mem_of_forall_mem_localizedAt_prime (M : Submodule A V) {v : V}
    (h : ∀ 𝔭 : PrimeSpectrum A, v ∈ M.localizedAt 𝔭.asIdeal.primeCompl) :
    v ∈ M :=
  mem_of_forall_mem_localizedAt_maximal M fun 𝔪 =>
    h ⟨𝔪.asIdeal, 𝔪.isMaximal.isPrime⟩

/-- **A submodule is the intersection of its saturations at the maximal ideals.** Let $A$ be a
commutative ring, $V$ an $A$-module and $M$ a submodule of $V$. For a maximal ideal
$\mathfrak m$ of $A$, let $M_{\mathfrak m}$ be the saturation of $M$ at $A \setminus \mathfrak m$,
that is, the set of $v \in V$ with $s v \in M$ for some $s \in A \setminus \mathfrak m$. Then $M$
is the intersection of the submodules $M_{\mathfrak m}$ over all maximal ideals $\mathfrak m$
of $A$.

Source: ATLAS NumberTheoryI, Section 2.3, Proposition 2.6, maximal-ideal form. -/
theorem eq_iInf_localizedAt_maximal (M : Submodule A V) :
    (⨅ 𝔪 : MaximalSpectrum A, M.localizedAt 𝔪.asIdeal.primeCompl) = M := by
  ext v
  simp only [Submodule.mem_iInf]
  constructor
  · intro hv
    exact mem_of_forall_mem_localizedAt_maximal M hv
  · intro hv 𝔪
    exact ⟨1, 𝔪.asIdeal.primeCompl.one_mem, by simpa using hv⟩

/-- **A submodule is the intersection of its saturations at the prime ideals.** Let $A$ be a
commutative ring, $V$ an $A$-module and $M$ a submodule of $V$. For a prime ideal
$\mathfrak p$ of $A$, let $M_{\mathfrak p}$ be the saturation of $M$ at $A \setminus \mathfrak p$,
that is, the set of $v \in V$ with $s v \in M$ for some $s \in A \setminus \mathfrak p$. Then $M$
is the intersection of the submodules $M_{\mathfrak p}$ over all prime ideals $\mathfrak p$
of $A$.

Source: ATLAS NumberTheoryI, Section 2.3, Proposition 2.6, prime-ideal form. -/
theorem eq_iInf_localizedAt_prime (M : Submodule A V) :
    (⨅ 𝔭 : PrimeSpectrum A, M.localizedAt 𝔭.asIdeal.primeCompl) = M := by
  ext v
  simp only [Submodule.mem_iInf]
  constructor
  · intro hv
    exact mem_of_forall_mem_localizedAt_prime M hv
  · intro hv 𝔭
    exact ⟨1, 𝔭.asIdeal.primeCompl.one_mem, by simpa using hv⟩

/-- **Intersections of saturations over maximal and over prime ideals agree.** Let $A$ be a
commutative ring, $V$ an $A$-module and $M$ a submodule of $V$. For a prime ideal $\mathfrak p$
of $A$, let $M_{\mathfrak p}$ be the saturation of $M$ at $A \setminus \mathfrak p$, that is,
the set of $v \in V$ with $s v \in M$ for some $s \in A \setminus \mathfrak p$. Then the
intersection of the $M_{\mathfrak m}$ over all maximal ideals $\mathfrak m$ of $A$ equals the
intersection of the $M_{\mathfrak p}$ over all prime ideals $\mathfrak p$ of $A$. -/
theorem eq_iInf_localizedAt_maximal_eq_prime (M : Submodule A V) :
    (⨅ 𝔪 : MaximalSpectrum A, M.localizedAt 𝔪.asIdeal.primeCompl) =
    (⨅ 𝔭 : PrimeSpectrum A, M.localizedAt 𝔭.asIdeal.primeCompl) := by
  rw [eq_iInf_localizedAt_maximal, eq_iInf_localizedAt_prime]

end Submodule
