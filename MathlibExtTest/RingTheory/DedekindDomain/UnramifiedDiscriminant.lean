/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.UnramifiedDiscriminant

@[expose] public section

/-!
# Tests for unramified above a prime iff the prime does not divide the discriminant ideal

Generic application examples exercising
`Ideal.isUnramifiedAt_iff_not_dvd_discriminantIdeal` (ATLAS Theorem 12.19,
discriminant half), plus the contrapositive form: `𝔭` divides the discriminant
ideal if and only if some prime above `𝔭` is ramified. These are API/inference
tests; no new definitions are introduced.
-/

set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

universe u

namespace UnramifiedDiscriminantTest

open Ideal

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
  [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B]

omit [FiniteDimensional K L] [IsIntegralClosure B A L] in
include K L in
/-- Transport the original fraction-field presentation for the original clients. -/
private theorem isSeparable_fractionRing :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

/-- Generic application of the discriminant-half iff. -/
example (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) ↔
    ¬ (𝔭.asIdeal ∣ discriminantIdeal A B) := by
  have hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_fractionRing A K L B
  exact Ideal.isUnramifiedAt_iff_not_dvd_discriminantIdeal A B 𝔭

/-- Generic application of the forward implication. -/
example (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hall : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) :
    ¬ (𝔭.asIdeal ∣ discriminantIdeal A B) := by
  have hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_fractionRing A K L B
  exact Ideal.not_dvd_discriminantIdeal_of_isUnramifiedAt A B 𝔭 hall

/-- Generic application of the reverse implication. -/
example (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hndvd : ¬ (𝔭.asIdeal ∣ discriminantIdeal A B))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B) (hlies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    Algebra.IsUnramifiedAt A 𝔮.asIdeal := by
  have hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_fractionRing A K L B
  exact Ideal.isUnramifiedAt_of_not_dvd_discriminantIdeal A B 𝔭 hndvd 𝔮 hlies

omit [FiniteDimensional K L] [IsIntegralClosure B A L] in
include K L in
/-- Contrapositive form: `𝔭` divides the discriminant ideal if and only if
some prime above `𝔭` is ramified. -/
theorem dvd_discriminantIdeal_iff_exists_ramified
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    (𝔭.asIdeal ∣ discriminantIdeal A B) ↔
      ∃ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt A 𝔮.asIdeal := by
  have hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_fractionRing A K L B
  rw [← not_iff_not]
  push Not
  exact (Ideal.isUnramifiedAt_iff_not_dvd_discriminantIdeal A B 𝔭).symm

#print axioms Ideal.isUnramifiedAt_iff_not_dvd_discriminantIdeal
#print axioms Ideal.not_dvd_discriminantIdeal_of_isUnramifiedAt
#print axioms Ideal.isUnramifiedAt_of_not_dvd_discriminantIdeal
#print axioms UnramifiedDiscriminantTest.dvd_discriminantIdeal_iff_exists_ramified

end UnramifiedDiscriminantTest
