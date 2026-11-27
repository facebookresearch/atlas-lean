/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.ArtinConductor

@[expose] public section

open NumberField IsDedekindDomain

universe u v

example (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M]
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ ArtinConductor.conductor ψ ↔
      ¬ ArtinConductor.IsUnramifiedAt ψ v :=
  ArtinConductor.dvd_conductor_iff_not_isUnramifiedAt K M ψ v

example (K : Type 1) (M : Type 2) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M]
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ ArtinConductor.conductor ψ ↔
      ¬ ArtinConductor.IsUnramifiedAt ψ v :=
  ArtinConductor.dvd_conductor_iff_not_isUnramifiedAt K M ψ v

example (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (v : HeightOneSpectrum (𝓞 K)) :
    ArtinConductor.IsUnramifiedAt (K := K) (M := M) (1 : (M ≃ₐ[K] M) →* ℂˣ) v := by
  intro σ _
  simp

example (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ ArtinConductor.conductor (1 : (M ≃ₐ[K] M) →* ℂˣ) := by
  intro h
  exact (ArtinConductor.dvd_conductor_iff_not_isUnramifiedAt K M 1 v).1 h
    (by intro σ _; simp)

example (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (v : HeightOneSpectrum (𝓞 K)) :
    (ArtinConductor.primeAbove K M v).under (𝓞 K) = v.asIdeal :=
  ArtinConductor.under_primeAbove (K := K) (M := M) v
