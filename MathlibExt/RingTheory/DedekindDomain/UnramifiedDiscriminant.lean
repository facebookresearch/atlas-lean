/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.DiscriminantTower


attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

@[expose] public section

/-!
# Standard unramified-in criterion for the discriminant ideal

ATLAS `NumberTheoryI`, Theorem 12.19 (discriminant half). Let `A` be a Dedekind
domain with fraction field `K`, let `L / K` be a finite separable extension, and
let `B` be the integral closure of `A` in `L`. For a nonzero prime `𝔭` of `A`,
the extension satisfies Mathlib's standard `Algebra.IsUnramifiedIn B 𝔭.asIdeal`
if and only if `𝔭` does not divide the discriminant ideal of `B / A`.

The discriminant ideal is `Ideal.discriminantIdeal A B` from
`MathlibExt.RingTheory.DedekindDomain.DiscriminantTower`, defined as
`Ideal.spanNorm A (differentIdeal A B)`
(`Ideal.discriminantIdeal_eq_spanNorm`), hence also `Ideal.relNorm A`
of the different ideal (`Ideal.spanNorm_eq`); those unfolding lemmas are
used only inside the proofs below. The different-ideal half of the book's statement,
`𝔮 ∤ differentIdeal A B ↔ Algebra.IsUnramifiedAt A 𝔮`, is Mathlib's
`not_dvd_differentIdeal_iff`, used as a lemma, not re-proved.

The proof adapts `unramified_iff_not_dvd_discriminant` in
`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`. That formalization
transports fraction-field separability, factors the different, maps its prime
factors through the relative norm, and applies the different-ideal criterion.
Here the public statements assume fraction-ring separability directly and use
the discriminant ideal as the norm of the different instead of the archived
lattice/submodule representation. The ideal argument is retained: the forward
direction factors the different ideal into primes
(`Ideal.prod_normalizedFactors_eq_self`) and uses that the relative norm of a
prime above `𝔭` is a power of `𝔭` (`Ideal.exists_relNorm_eq_pow_of_isPrime`);
the reverse direction uses `Ideal.relNorm_le_comap` together with the same
power statement.

## Main results

* `Ideal.isUnramifiedIn_iff_not_dvd_discriminantIdeal`: the standard primary
  discriminant-half of Theorem 12.19, with direct `A`/`B` hypotheses.
* `Ideal.isUnramifiedAt_iff_not_dvd_discriminantIdeal`,
  `Ideal.isUnramifiedAt_of_not_dvd_discriminantIdeal`, and
  `Ideal.not_dvd_discriminantIdeal_of_isUnramifiedAt`: the original height-one
  statements, now derived compatibility results of the primary criterion.

The standard predicate quantifies over every prime ideal of `B` above `𝔭`.
Such a prime is nonzero by `Ideal.ne_bot_of_liesOver_of_ne_bot`; hence the
height-one formulation is equivalent here. The ideal arguments remain private
proof helpers. No separate public height-one proof engine or new predicate is
introduced.
-/

namespace Ideal

/-- Every prime over the nonzero base prime is nonzero, so the standard
unramified-in predicate is equivalent to the height-one formulation. -/
private theorem isUnramifiedIn_iff_forall_heightOne
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    Algebra.IsUnramifiedIn B 𝔭.asIdeal ↔
      ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B,
        𝔮.asIdeal.LiesOver 𝔭.asIdeal → Algebra.IsUnramifiedAt A 𝔮.asIdeal := by
  constructor
  · intro h 𝔮 hlies
    exact h 𝔮.asIdeal 𝔮.isPrime hlies
  · intro h P hPprime hPlies
    let : P.IsPrime := hPprime
    let : P.LiesOver 𝔭.asIdeal := hPlies
    exact h ⟨P, hPprime, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P⟩ hPlies

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- If the extension is unramified at every prime above `𝔭`, then `𝔭` does not
divide the discriminant ideal. -/
private theorem not_dvd_discriminantIdeal_of_heightOne_core
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hall : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) :
    ¬ (𝔭.asIdeal ∣ discriminantIdeal A B) := by
  have hDne : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  rw [discriminantIdeal_eq_spanNorm A B, spanNorm_eq]
  intro hdvd
  have hprod : relNorm A (differentIdeal A B) =
      ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal A B)).map
        (relNorm A)).prod := by
    conv_lhs => rw [← prod_normalizedFactors_eq_self hDne]
    rw [map_multiset_prod]
  rw [hprod] at hdvd
  obtain ⟨Q, hQmem, hQdvd⟩ := 𝔭.prime.exists_mem_multiset_map_dvd hdvd
  have hQprime : Q.IsPrime := (mem_normalizedFactors_iff hDne).mp hQmem |>.1
  have hQle : differentIdeal A B ≤ Q := (mem_normalizedFactors_iff hDne).mp hQmem |>.2
  have hQdvdD : Q ∣ differentIdeal A B := Ideal.dvd_iff_le.mpr hQle
  have hQne : Q ≠ ⊥ := by
    intro hQ
    rw [hQ] at hQle
    exact hDne (le_antisymm hQle bot_le)
  obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime Q (Q.under A)
  rw [hs] at hQdvd
  have hp_dvd_under : 𝔭.asIdeal ∣ Q.under A := 𝔭.prime.dvd_of_dvd_pow hQdvd
  have hunder_max : (Q.under A).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime
      (fun h => hQne (Ideal.eq_bot_of_under_eq_bot h)) inferInstance
  have heq : Q.under A = 𝔭.asIdeal :=
    hunder_max.eq_of_le 𝔭.isPrime.ne_top (Ideal.dvd_iff_le.mp hp_dvd_under)
  have hQlies : Q.LiesOver 𝔭.asIdeal := ⟨heq.symm⟩
  have hunram := hall ⟨Q, hQprime, hQne⟩ hQlies
  exact (not_dvd_differentIdeal_iff.mpr hunram) hQdvdD

/-- If `𝔭` does not divide the discriminant ideal, then the extension is
unramified at every prime above `𝔭`. -/
private theorem heightOne_isUnramifiedAt_of_not_dvd_core
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hndvd : ¬ (𝔭.asIdeal ∣ discriminantIdeal A B))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B) (hlies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    Algebra.IsUnramifiedAt A 𝔮.asIdeal := by
  rw [discriminantIdeal_eq_spanNorm A B, spanNorm_eq] at hndvd
  rw [← not_dvd_differentIdeal_iff]
  intro hqdvd
  apply hndvd
  have h1 : 𝔭.asIdeal ∣ relNorm A 𝔮.asIdeal := by
    obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime 𝔮.asIdeal 𝔭.asIdeal
    have hle : relNorm A 𝔮.asIdeal ≤ 𝔭.asIdeal := by
      calc relNorm A 𝔮.asIdeal
          ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal := relNorm_le_comap A 𝔮.asIdeal
        _ = 𝔭.asIdeal := by rw [← Ideal.under_def]; exact hlies.over.symm
    rw [hs] at hle
    have hspos : 0 < s := by
      by_contra h
      push Not at h
      rw [Nat.le_zero.mp h, pow_zero, one_eq_top] at hle
      exact 𝔭.isPrime.ne_top (top_unique hle)
    rw [hs]
    exact dvd_pow_self _ hspos.ne'
  have h2 : relNorm A 𝔮.asIdeal ∣ relNorm A (differentIdeal A B) := by
    rw [Ideal.dvd_iff_le]
    exact relNorm_mono A (Ideal.dvd_iff_le.mp hqdvd)
  exact dvd_trans h1 h2


/-- Theorem 12.19, discriminant half, in Mathlib's standard predicate:
`𝔭` is unramified in `B` exactly when it does not divide the discriminant ideal. -/
theorem isUnramifiedIn_iff_not_dvd_discriminantIdeal
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    Algebra.IsUnramifiedIn B 𝔭.asIdeal ↔
      ¬ (𝔭.asIdeal ∣ discriminantIdeal A B) :=
  (isUnramifiedIn_iff_forall_heightOne A B 𝔭).trans
    ⟨not_dvd_discriminantIdeal_of_heightOne_core A B 𝔭,
     fun hndvd 𝔮 hlies =>
       heightOne_isUnramifiedAt_of_not_dvd_core A B 𝔭 hndvd 𝔮 hlies⟩

/-- Height-one compatibility: derive nondivisibility from the standard
unramified-in criterion after converting the original height-one premise. -/
theorem not_dvd_discriminantIdeal_of_isUnramifiedAt
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hall : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) :
    ¬ (𝔭.asIdeal ∣ discriminantIdeal A B) :=
  (isUnramifiedIn_iff_not_dvd_discriminantIdeal A B 𝔭).mp
    ((isUnramifiedIn_iff_forall_heightOne A B 𝔭).mpr hall)

/-- Height-one compatibility: evaluate the standard unramified-in conclusion
at the particular height-one prime supplied by an original client. -/
theorem isUnramifiedAt_of_not_dvd_discriminantIdeal
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hndvd : ¬ (𝔭.asIdeal ∣ discriminantIdeal A B))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B) (hlies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    Algebra.IsUnramifiedAt A 𝔮.asIdeal :=
  (isUnramifiedIn_iff_not_dvd_discriminantIdeal A B 𝔭).mpr hndvd
    𝔮.asIdeal 𝔮.isPrime hlies

/-- The original height-one formulation, derived from the standard primary criterion. -/
theorem isUnramifiedAt_iff_not_dvd_discriminantIdeal
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) ↔
    ¬ (𝔭.asIdeal ∣ discriminantIdeal A B) :=
  (isUnramifiedIn_iff_forall_heightOne A B 𝔭).symm.trans
    (isUnramifiedIn_iff_not_dvd_discriminantIdeal A B 𝔭)

end Ideal
