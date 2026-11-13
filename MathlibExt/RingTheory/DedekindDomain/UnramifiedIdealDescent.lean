/-
Copyright (c) the flt-regular authors and 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0.

Adapted from P2M/Sol/S_flt_regular.lean, lines 2418–2510, at
anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The source attributes this material to flt-regular,
FltRegular/NumberTheory/Unramified.lean, by Alex J. Best, Christopher Birkbeck,
Riccardo Brasca, Eric Rodriguez Boidi, Ruben Van de Velde and Andrew Yang.
See that source's NOTICE and ATTRIBUTION.md, section 3.
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Descent of invariant ideals in an unramified extension

An ideal in the integral closure of a Dedekind domain in a finite Galois
extension is extended from its contraction if the extension is unramified and
the ideal is fixed by every Galois automorphism. Ideals may be zero or
nonradical.

The proof groups canonical integral-ideal factors into Galois orbits, retaining
their multiplicities. Unramifiedness identifies each prime-fiber product with
the extension of the contracted prime.
-/

public section

open UniqueFactorizationMonoid

namespace Ideal

private lemma prod_primesOverFinset_eq_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [Algebra.Unramified R S]
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    ∏ P ∈ _root_.IsDedekindDomain.primesOverFinset p S, P =
      p.map (algebraMap R S) := by
  classical
  have hmap : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  rw [← associated_iff_eq.mp (factors_pow_count_prod hmap)]
  apply Finset.prod_congr rfl
  intro P hP
  have : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  have hP' := (_root_.IsDedekindDomain.mem_primesOverFinset_iff hp S).mp hP
  have : P.IsPrime := hP'.1
  have : P.LiesOver p := hP'.2
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count p P hmap,
    ramificationIdx_eq_one_of_isUnramifiedAt, pow_one]

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Field K] [Field L] [IsDedekindDomain R]
  [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [IsIntegralClosure S R L]
  [FiniteDimensional K L]

/-- In an unramified finite Galois extension, every invariant integral ideal
is the extension of its contraction. This includes zero and nonradical ideals.

Adapted from `FltRegular.comap_map_eq_of_unramified`, source lines 2437–2510.
The order `map_comap` in this name follows the actual extension-of-contraction
conclusion, rather than the reversed order in the source name. -/
theorem map_comap_eq_of_unramified_of_galois_invariant
    [IsGalois K L] [Algebra.Unramified R S] (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain _
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  by_cases hIbot : I = ⊥
  · subst I
    exact map_comap_bot
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have hcontract : I.comap (algebraMap R S) ≠ ⊥ :=
    mt Ideal.eq_bot_of_under_eq_bot hIbot
  have hlying : ∀ p, (p.IsPrime ∧ I.comap (algebraMap R S) ≤ p) →
      ∃ P ≥ I, P ∈ primesOver p S := by
    intro p ⟨hp, hle⟩
    obtain ⟨P, hIP, hP, hover⟩ :=
      exists_ideal_over_prime_of_isIntegral _ _ hle
    exact ⟨P, hIP, hP, ⟨hover.symm⟩⟩
  choose Q hQ hQover using hlying
  suffices I = ∏ p ∈ (factors (I.comap (algebraMap R S))).toFinset,
      (p.map (algebraMap R S)) ^
        (if h : p.IsPrime ∧ I.comap (algebraMap R S) ≤ p then
          (factors I).count (Q p h) else 0) by
    simp_rw [← Ideal.mapHom_apply, ← map_pow, ← map_prod,
      Ideal.mapHom_apply] at this
    rw [this, map_comap_map]
  conv_lhs => rw [← associated_iff_eq.mp (factors_pow_count_prod hIbot)]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := (Ideal.comap (algebraMap R S) : Ideal S → Ideal R))
    (t := (factors (I.comap (algebraMap R S))).toFinset)]
  · apply Finset.prod_congr rfl
    intro p hp
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hcontract] at hp
    have hpbot : p ≠ ⊥ := fun h ↦ hcontract (eq_bot_iff.mpr (hp.2.trans_eq h))
    have := hp.1
    rw [← prod_primesOverFinset_eq_map p hpbot, ← Finset.prod_pow]
    have : p.IsMaximal := hp.1.isMaximal hpbot
    apply Finset.prod_congr
    · ext P
      rw [factors_eq_normalizedFactors, Finset.mem_filter,
        Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hIbot,
        ← Finset.mem_coe, _root_.IsDedekindDomain.coe_primesOverFinset hpbot S]
      refine ⟨fun h ↦ ⟨h.1.1, ⟨h.2.symm⟩⟩,
        fun h ↦ ⟨⟨h.1, ?_⟩, ?_⟩⟩
      · obtain ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (hQover p hp) h
        rw [← hσ, ← hI σ]
        exact Ideal.comap_mono (hQ p hp)
      · exact h.2.1.symm
    · intro P hP
      rw [← Finset.mem_coe,
        _root_.IsDedekindDomain.coe_primesOverFinset hpbot S] at hP
      congr 1
      rw [dite_eq_left hp, ← Nat.cast_inj (R := ENat), ← normalize_eq P,
        factors_eq_normalizedFactors,
        ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot hP).irreducible hIbot,
        ← normalize_eq (Q p hp),
        ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot (hQover p hp)).irreducible hIbot,
        emultiplicity_eq_emultiplicity_iff]
      intro n
      obtain ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (hQover p hp) hP
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le]
      conv_lhs => rw [← hI σ, ← hσ,
        Ideal.comap_le_iff_le_map _ (AlgEquiv.bijective _), Ideal.map_pow,
        Ideal.map_comap_of_surjective _ (AlgEquiv.surjective _)]
  · intro P hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot] at hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hcontract]
    exact ⟨hP.1.comap _, Ideal.comap_mono hP.2⟩

end Ideal
