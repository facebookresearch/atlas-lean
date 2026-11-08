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

/-- The saturation of a submodule `M` at a submonoid `S` of the scalar
ring: the elements `v` for which some `s ∈ S` has `s • v ∈ M`. This is
the contraction to `V` of the extension of `M` to the localization at
`S`. -/
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

/-- Membership in the saturation at `S`: `v` lies in
`M.localizedAt S` iff some `s ∈ S` has `s • v ∈ M`. -/
theorem mem_localizedAt {M : Submodule A V} {S : Submonoid A} {v : V} :
    v ∈ M.localizedAt S ↔ ∃ s ∈ S, s • v ∈ M :=
  Iff.rfl

/-- Proposition 2.6, element form at the maximal ideals: if `v` lies
in the localization of `M` at every maximal ideal, then `v ∈ M`. -/
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

/-- Proposition 2.6, element form at the prime ideals: if `v` lies in
the localization of `M` at every prime ideal, then `v ∈ M`. -/
theorem mem_of_forall_mem_localizedAt_prime (M : Submodule A V) {v : V}
    (h : ∀ 𝔭 : PrimeSpectrum A, v ∈ M.localizedAt 𝔭.asIdeal.primeCompl) :
    v ∈ M :=
  mem_of_forall_mem_localizedAt_maximal M fun 𝔪 =>
    h ⟨𝔪.asIdeal, 𝔪.isMaximal.isPrime⟩

/-- Proposition 2.6, maximal-ideal form: a submodule equals the
intersection of its localizations at the maximal ideals. -/
theorem eq_iInf_localizedAt_maximal (M : Submodule A V) :
    (⨅ 𝔪 : MaximalSpectrum A, M.localizedAt 𝔪.asIdeal.primeCompl) = M := by
  ext v
  simp only [Submodule.mem_iInf]
  constructor
  · intro hv
    exact mem_of_forall_mem_localizedAt_maximal M hv
  · intro hv 𝔪
    exact ⟨1, 𝔪.asIdeal.primeCompl.one_mem, by simpa using hv⟩

/-- Proposition 2.6, prime-ideal form: a submodule equals the
intersection of its localizations at the prime ideals. -/
theorem eq_iInf_localizedAt_prime (M : Submodule A V) :
    (⨅ 𝔭 : PrimeSpectrum A, M.localizedAt 𝔭.asIdeal.primeCompl) = M := by
  ext v
  simp only [Submodule.mem_iInf]
  constructor
  · intro hv
    exact mem_of_forall_mem_localizedAt_prime M hv
  · intro hv 𝔭
    exact ⟨1, 𝔭.asIdeal.primeCompl.one_mem, by simpa using hv⟩

/-- The intersections of the localizations at the maximal ideals and
at the prime ideals agree. -/
theorem eq_iInf_localizedAt_maximal_eq_prime (M : Submodule A V) :
    (⨅ 𝔪 : MaximalSpectrum A, M.localizedAt 𝔪.asIdeal.primeCompl) =
    (⨅ 𝔭 : PrimeSpectrum A, M.localizedAt 𝔭.asIdeal.primeCompl) := by
  rw [eq_iInf_localizedAt_maximal, eq_iInf_localizedAt_prime]

end Submodule
