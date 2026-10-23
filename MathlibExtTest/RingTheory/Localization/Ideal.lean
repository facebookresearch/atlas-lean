/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Localization.Ideal
public import Mathlib.Data.Nat.Prime.Int

@[expose] public section

/-- The maximal-ideal intersection at `⊤` over `ℤ`. -/
example : (⨅ 𝔪 : MaximalSpectrum ℤ,
    ((⊤ : Ideal ℤ).map
      (algebraMap ℤ (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap ℤ (Localization 𝔪.asIdeal.primeCompl))) = ⊤ :=
  Ideal.eq_iInf_comap_map_localization_maximal ⊤

/-- The prime-ideal intersection at `⊤` over `ℤ`. -/
example : (⨅ 𝔭 : PrimeSpectrum ℤ,
    ((⊤ : Ideal ℤ).map
      (algebraMap ℤ (Localization 𝔭.asIdeal.primeCompl))).comap
        (algebraMap ℤ (Localization 𝔭.asIdeal.primeCompl))) = ⊤ :=
  Ideal.eq_iInf_comap_map_localization_prime ⊤

/-- The maximal- and prime-ideal intersections agree at `(6)` over `ℤ`. -/
example : (⨅ 𝔪 : MaximalSpectrum ℤ,
    ((Ideal.span {(6 : ℤ)}).map
      (algebraMap ℤ (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap ℤ (Localization 𝔪.asIdeal.primeCompl))) =
    (⨅ 𝔭 : PrimeSpectrum ℤ,
      ((Ideal.span {(6 : ℤ)}).map
        (algebraMap ℤ (Localization 𝔭.asIdeal.primeCompl))).comap
          (algebraMap ℤ (Localization 𝔭.asIdeal.primeCompl))) :=
  Ideal.iInf_comap_map_localization_maximal_eq_prime _

/-- Membership in `(6)` over `ℤ` via the maximal-ideal intersection:
every element of every localization contraction is in the ideal. -/
example : (6 : ℤ) ∈ Ideal.span {(6 : ℤ)} := by
  rw [← Ideal.eq_iInf_comap_map_localization_maximal
    (Ideal.span {(6 : ℤ)})]
  simp only [Ideal.mem_iInf]
  intro 𝔪
  rw [Ideal.mem_comap]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self 6)

/-- Membership in `(6)` over `ℤ` via the prime-ideal intersection. -/
example : (6 : ℤ) ∈ Ideal.span {(6 : ℤ)} := by
  rw [← Ideal.eq_iInf_comap_map_localization_prime
    (Ideal.span {(6 : ℤ)})]
  simp only [Ideal.mem_iInf]
  intro 𝔭
  rw [Ideal.mem_comap]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self 6)

/-- Contraction of `(6)` at the maximal ideal `(2)` over `ℤ` is `(2)`:
localizing at `(2)` inverts `3`, so `6` and `2` generate the same ideal. -/
example (𝔪 : MaximalSpectrum ℤ) (h𝔪 : 𝔪.asIdeal = Ideal.span {(2 : ℤ)}) :
    ((Ideal.span {(6 : ℤ)}).map
        (algebraMap ℤ (Localization 𝔪.asIdeal.primeCompl))).comap
      (algebraMap ℤ (Localization 𝔪.asIdeal.primeCompl)) =
    Ideal.span {(2 : ℤ)} := by
  ext x
  rw [Ideal.mem_comap,
    IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪.asIdeal.primeCompl]
  simp only [Ideal.mem_span_singleton]
  have h2prime : Prime (2 : ℤ) := Int.prime_two
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [Ideal.mem_primeCompl_iff, h𝔪, Ideal.mem_span_singleton] at hs
    have h2dvd : (2 : ℤ) ∣ s * x := dvd_trans (by norm_num) hsx
    rcases (h2prime.dvd_mul.mp h2dvd) with h | h
    · exact absurd h hs
    · exact h
  · intro hx
    refine ⟨3, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff, h𝔪, Ideal.mem_span_singleton]
      norm_num
    · obtain ⟨c, hc⟩ := hx
      exact ⟨c, by rw [hc]; ring⟩
